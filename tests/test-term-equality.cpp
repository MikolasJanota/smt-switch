/*********************                                                        */
/*! \file test-term-equality.cpp
 ** \verbatim
 ** This file is part of the smt-switch project.
 ** Copyright (c) 2026 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Tests for term equality and hashing.
 **
 **/

#include <cstdint>
#include <string>

#include "available_solvers.h"
#include "gtest/gtest.h"
#include "smt.h"

using namespace smt;

namespace smt_tests {

GTEST_ALLOW_UNINSTANTIATED_PARAMETERIZED_TEST(TermEqualityTests);
class TermEqualityTests
    : public ::testing::Test,
      public ::testing::WithParamInterface<SolverConfiguration>
{
 protected:
  void SetUp() override { s = create_solver(GetParam()); }
  SmtSolver s;

  static void expect_distinct_terms(const Term & a,
                                    const Term & b,
                                    const std::string & label)
  {
    EXPECT_NE(a, b) << label << ": terms compare equal";

    UnorderedTermSet set;
    set.insert(a);
    set.insert(b);
    EXPECT_EQ(set.size(), 2) << label << ": UnorderedTermSet collapsed terms";
    EXPECT_EQ(set.count(a), 1) << label << ": set lost first term";
    EXPECT_EQ(set.count(b), 1) << label << ": set lost second term";

    UnorderedTermMap map;
    map[a] = a;
    map[b] = b;
    EXPECT_EQ(map.size(), 2) << label << ": UnorderedTermMap collapsed keys";
    EXPECT_EQ(map.at(a), a) << label << ": map lookup for first key is wrong";
    EXPECT_EQ(map.at(b), b) << label << ": map lookup for second key is wrong";
  }
};

TEST_P(TermEqualityTests, SignedNumeralIdentity)
{
  Sort intsort = s->make_sort(INT);

  Term pos9_i64 = s->make_term(std::int64_t(9), intsort);
  Term neg9_i64 = s->make_term(std::int64_t(-9), intsort);
  Term pos9_str = s->make_term("9", intsort);
  Term neg9_str = s->make_term("-9", intsort);
  Term pos10 = s->make_term(std::int64_t(10), intsort);
  Term neg10 = s->make_term(std::int64_t(-10), intsort);
  Term zero = s->make_term(std::int64_t(0), intsort);

  EXPECT_EQ(pos9_i64, pos9_str);
  EXPECT_EQ(neg9_i64, neg9_str);

  expect_distinct_terms(pos9_i64, neg9_i64, "9 vs -9");
  expect_distinct_terms(pos9_str, neg9_str, "string 9 vs string -9");
  expect_distinct_terms(pos10, neg10, "10 vs -10");
  expect_distinct_terms(zero, neg9_i64, "0 vs -9");
}

INSTANTIATE_TEST_SUITE_P(ParameterizedSolverTermEqualityTests,
                         TermEqualityTests,
                         testing::ValuesIn(filter_solver_configurations(
                             { THEORY_INT })));

}  // namespace smt_tests
