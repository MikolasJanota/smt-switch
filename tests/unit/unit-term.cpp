/*********************                                                        */
/*! \file unit-term.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Unit tests for terms.
**
**
**/

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;
using namespace std;

namespace smt_tests {

void expect_distinct_terms(const Term & a, const Term & b)
{
  EXPECT_NE(a, b);

  UnorderedTermSet terms;
  terms.insert(a);
  terms.insert(b);
  EXPECT_EQ(terms.size(), 2);
  EXPECT_EQ(terms.count(a), 1);
  EXPECT_EQ(terms.count(b), 1);

  UnorderedTermMap term_map;
  term_map[a] = a;
  term_map[b] = b;
  EXPECT_EQ(term_map.size(), 2);
  EXPECT_EQ(term_map.at(a), a);
  EXPECT_EQ(term_map.at(b), b);
}

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTermTests);
class UnitTermTests : public ::testing::Test,
                      public testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());

    boolsort = s->make_sort(BOOL);
    bvsort = s->make_sort(BV, 4);
    funsort = s->make_sort(FUNCTION, SortVec{ bvsort, bvsort });
    arrsort = s->make_sort(ARRAY, bvsort, bvsort);
  }
  SmtSolver s;
  Sort boolsort, bvsort, funsort, arrsort;
};

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(UnitTermParamTests);
class UnitTermParamTests : public UnitTermTests
{
};

TEST_P(UnitTermTests, FunOp)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  ASSERT_TRUE(x->is_symbol());
  ASSERT_TRUE(x->is_symbolic_const());
  ASSERT_TRUE(f->is_symbol());
  ASSERT_FALSE(f->is_symbolic_const());
}

TEST_P(UnitTermTests, Classification)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term true_term = s->make_term(true);
  Term bv_three = s->make_term(3, bvsort);
  Term fx = s->make_term(Apply, f, x);

  EXPECT_TRUE(x->is_symbol());
  EXPECT_TRUE(x->is_symbolic_const());
  EXPECT_FALSE(x->is_param());
  EXPECT_FALSE(x->is_value());
  EXPECT_TRUE(x->get_op().is_null());
  EXPECT_EQ(x->get_sort(), bvsort);

  EXPECT_FALSE(true_term->is_symbol());
  EXPECT_FALSE(true_term->is_symbolic_const());
  EXPECT_FALSE(true_term->is_param());
  EXPECT_TRUE(true_term->is_value());
  EXPECT_EQ(true_term->get_sort(), boolsort);

  EXPECT_FALSE(bv_three->is_symbol());
  EXPECT_TRUE(bv_three->is_value());
  EXPECT_EQ(bv_three->get_sort(), bvsort);
  EXPECT_EQ(bv_three->to_int(), 3);

  EXPECT_FALSE(fx->is_symbol());
  EXPECT_FALSE(fx->is_symbolic_const());
  EXPECT_FALSE(fx->is_param());
  EXPECT_FALSE(fx->is_value());
  EXPECT_EQ(fx->get_op(), Apply);
  EXPECT_EQ(fx->get_sort(), bvsort);
}

TEST_P(UnitTermTests, ApplicationChildren)
{
  Term x = s->make_symbol("x", bvsort);
  Term f = s->make_symbol("f", funsort);
  Term fx = s->make_term(Apply, f, x);

  TermVec children(fx->begin(), fx->end());
  ASSERT_EQ(children.size(), 2);
  EXPECT_EQ(children[0], f);
  EXPECT_EQ(children[1], x);
}

TEST_P(UnitTermTests, EqualityAndHashing)
{
  Term x = s->make_symbol("x", bvsort);
  Term y = s->make_symbol("y", bvsort);
  Term one = s->make_term(1, bvsort);
  Term one_again = s->make_term(1, bvsort);
  Term two = s->make_term(2, bvsort);

  EXPECT_EQ(one, one_again);
  EXPECT_EQ(one->hash(), one_again->hash());
  EXPECT_EQ(one->get_id(), one_again->get_id());
  expect_distinct_terms(one, two);
  expect_distinct_terms(x, y);

  Term x_plus_one = s->make_term(BVAdd, x, one);
  Term x_plus_one_again = s->make_term(BVAdd, x, one_again);
  Term y_plus_one = s->make_term(BVAdd, y, one);

  EXPECT_EQ(x_plus_one, x_plus_one_again);
  EXPECT_EQ(x_plus_one->hash(), x_plus_one_again->hash());
  EXPECT_EQ(x_plus_one->get_id(), x_plus_one_again->get_id());
  expect_distinct_terms(x_plus_one, y_plus_one);
}

TEST_P(UnitTermTests, Array)
{
  Term arr = s->make_symbol("arr", arrsort);
  ASSERT_TRUE(arr->is_symbol());
  ASSERT_TRUE(arr->is_symbolic_const());
  ASSERT_FALSE(arr->is_param());
  ASSERT_FALSE(arr->is_value());
  ASSERT_EQ(arr->get_sort(), arrsort);
}

TEST_P(UnitTermParamTests, ParamClassification)
{
  Term x = s->make_param("x", bvsort);

  EXPECT_TRUE(x->is_symbol());
  EXPECT_FALSE(x->is_symbolic_const());
  EXPECT_TRUE(x->is_param());
  EXPECT_FALSE(x->is_value());
  EXPECT_TRUE(x->get_op().is_null());
  EXPECT_EQ(x->get_sort(), bvsort);
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverUnitTerm,
                         UnitTermTests,
                         testing::ValuesIn(available_solver_configurations()));

INSTANTIATE_TEST_SUITE_P(
    ParameterizedSolverUnitTermParams,
    UnitTermParamTests,
    testing::ValuesIn(filter_solver_configurations({ QUANTIFIERS })));

}  // namespace smt_tests
