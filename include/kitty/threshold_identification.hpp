/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h>
#include "operators.hpp"
#include "operations.hpp"
#include "isop.hpp"
#include "traits.hpp"

namespace kitty
{
  //struct Constraint
  //{
    /* ILP defined as:
     * v[0] + v[1] + ... + const [>= | <=] v[N] */
    //std::vector<int64_t> variables;
    //uint64_t constant;
    //Constraint_Type type;
  //};

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  std::vector<uint64_t> neg_unate;

  auto numvars = tt.num_vars();
  auto ttf = tt;

  /* check for unateness, and create positive unate function */
  for ( auto i = 0u; i < numvars; i++ )
  {
    auto const tt1 = cofactor0( ttf, i );
    auto const tt2 = cofactor1( ttf, i );
    auto const smoothing = tt1 | tt2;

    if ( tt1 == tt2 )
    {
      /* don't care */
      continue;
    }
    else if ( tt1 == smoothing )
    {
      /* negative unate, convert to positive unate */
      flip_inplace( ttf, i );
      neg_unate.push_back( i );
    }
    else if ( tt2 != smoothing )
    {
      /* binate, tt is non-TF */
      return false;
    }
  }

  /* ttf is positive unate, build ILP problem */

  auto nttf = ~ttf;
  /* compute ISOPs */
  const auto fcubes = isop( ttf );
  const auto nfcubes = isop( nttf );
  unsigned ncol = numvars + 1;

  /* Create a new LP model */
  lprec *lp;
  int *colno = (int *) malloc( ncol * sizeof( int ) );
  REAL *row = (REAL *) malloc( ncol * sizeof( REAL ) );

  lp = make_lp( 0, ncol );
  if( lp == nullptr || colno == nullptr || row == nullptr ) {
    std::cerr << "Unable to create new LP model" << std::endl;
    return false;
  }
  if( colno == nullptr || row == nullptr ) {
    std::cerr << "Unable to allocate ILP constraints" << std::endl;
    return false;
  }

  set_verbose( lp, IMPORTANT );
  set_add_rowmode( lp, true );

  for ( auto cube : fcubes )
  {
    auto cnt = 0u;
    for ( auto i = 0u; i < numvars; i++ )
    {
      if ( cube.get_mask( i ) && cube.get_bit( i ) )
      {
        colno[cnt] = i + 1;
        row[cnt++] = 1;
      }
    }
    colno[cnt] = ncol;
    row[cnt++] = -1;

    if( !add_constraintex( lp, cnt, row, colno, GE, 0 ) ) {
      std::cerr << "Unable to add constraint" << std::endl;
      return false;
    }
  }

  for ( auto cube : nfcubes )
  {
    auto cnt = 0u;
    for ( auto i = 0u; i < numvars; i++ )
    {
      if ( !cube.get_mask( i ) || ( cube.get_mask( i ) && cube.get_bit( i ) ) )
      {
        colno[cnt] = i + 1;
        row[cnt++] = 1;
      }
    }
    colno[cnt] = ncol;
    row[cnt++] = -1;

    if( !add_constraintex( lp, cnt, row, colno, LE, -1 ) ) {
      std::cerr << "Unable to add constraint" << std::endl;
      return false;
    }
  }

  set_add_rowmode( lp, false );

  /* set the objective function */
  for ( auto i = 0u; i < ncol; i++ )
  {
    colno[i] = i + 1;
    row[i] = 1;
  }
  if( !set_obj_fnex( lp, ncol, row, colno ) ) {
    std::cerr << "Unable to add obj function" << std::endl;
    return false;
  }
  set_minim( lp );

  /* solve */
  auto result = solve(lp);

  /* if tt is non-TF: */
  if ( result != OPTIMAL && result != SUBOPTIMAL )
  {
    free( row );
    free( colno );
    delete_lp(lp);
    return false;
  }

  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  get_variables(lp, row);

  for ( auto i = 0u; i < ncol; i++ )
  {
    linear_form.push_back( static_cast<int64_t>( row[i] ) );
  }

  /* adjust for negative unate variables */
  for ( const auto var : neg_unate )
  {
    linear_form[var] = -linear_form[var];
    linear_form[ncol - 1] += linear_form[var];
  }

  *plf = linear_form;

  free( row );
  free( colno );
  delete_lp(lp);
  return true;
}

} /* namespace kitty */
