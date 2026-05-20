#include <cassert>
#include <cstdint>

#include "datatype.h"
#include "smt.h"
#include "z3_factory.h"

using namespace smt;

namespace {

Sort make_list_sort(const SmtSolver & solver)
{
  DatatypeDecl list_spec = solver->make_datatype_decl("list");
  DatatypeConstructorDecl nil_decl =
      solver->make_datatype_constructor_decl("nil");
  DatatypeConstructorDecl cons_decl =
      solver->make_datatype_constructor_decl("cons");
  solver->add_selector(cons_decl, "head", solver->make_sort(INT));
  solver->add_selector_self(cons_decl, "tail");
  solver->add_constructor(list_spec, nil_decl);
  solver->add_constructor(list_spec, cons_decl);
  return solver->make_sort(list_spec);
}

void test_linear_arithmetic(const SmtSolver & solver)
{
  Sort int_sort = solver->make_sort(INT);
  Term x = solver->make_symbol("x", int_sort);
  Term y = solver->make_symbol("y", int_sort);
  Term one = solver->make_term(1, int_sort);
  Term three = solver->make_term(3, int_sort);

  Term x_ge_one = solver->make_term(Ge, x, one);
  Term y_lt_x_plus_three =
      solver->make_term(Lt, y, solver->make_term(Plus, x, three));

  solver->assert_formula(x_ge_one);
  solver->assert_formula(y_lt_x_plus_three);
  assert(solver->check_sat().is_sat());

  solver->push();
  solver->assert_formula(solver->make_term(Lt, x, one));
  assert(solver->check_sat().is_unsat());
  solver->pop();
  assert(solver->check_sat().is_sat());
}

void test_bv_literals(const SmtSolver & solver)
{
  Sort bv_sort = solver->make_sort(BV, 7);

  Term binary_two = solver->make_term("0000010", bv_sort, 2);
  Term hex_fifteen = solver->make_term("0F", bv_sort, 16);

  assert(binary_two->is_value());
  assert(hex_fifteen->is_value());
  assert(binary_two->get_sort() == bv_sort);
  assert(hex_fifteen->get_sort() == bv_sort);
  assert(binary_two->to_int() == static_cast<std::uint64_t>(2));
  assert(hex_fifteen->to_int() == static_cast<std::uint64_t>(15));
}

void test_function_application(const SmtSolver & solver)
{
  Sort bool_sort = solver->make_sort(BOOL);
  Sort int_sort = solver->make_sort(INT);
  Sort real_sort = solver->make_sort(REAL);
  Sort function_sort = solver->make_sort(
      FUNCTION, SortVec{ bool_sort, int_sort, real_sort, bool_sort });

  Term function = solver->make_symbol("f", function_sort);
  Term app = solver->make_term(Apply,
                               TermVec{ function,
                                        solver->make_term(true),
                                        solver->make_term(1, int_sort),
                                        solver->make_term(2, real_sort) });

  assert(function->is_symbol());
  assert(function->get_sort() == function_sort);
  assert(function_sort->get_sort_kind() == FUNCTION);
  assert(function_sort->get_domain_sorts().size() == 3);
  assert(function_sort->get_codomain_sort() == bool_sort);
  assert(app->get_op() == Apply);
  assert(app->get_sort() == bool_sort);
}

void test_datatypes(const SmtSolver & solver)
{
  Sort list_sort = make_list_sort(solver);
  Datatype list_datatype = list_sort->get_datatype();
  Sort int_sort = solver->make_sort(INT);

  assert(list_sort->get_sort_kind() == DATATYPE);
  assert(list_datatype->get_name() == "list");
  assert(list_datatype->get_num_constructors() == 2);
  assert(list_datatype->get_num_selectors("nil") == 0);
  assert(list_datatype->get_num_selectors("cons") == 2);

  Term nil = solver->get_constructor(list_sort, "nil");
  Term cons = solver->get_constructor(list_sort, "cons");
  Term head = solver->get_selector(list_sort, "cons", "head");
  Term is_nil = solver->get_tester(list_sort, "nil");
  Term is_cons = solver->get_tester(list_sort, "cons");

  Term nil_term = solver->make_term(Apply_Constructor, nil);
  Term list_five = solver->make_term(
      Apply_Constructor, cons, solver->make_term(5, int_sort), nil_term);
  Term selected_head = solver->make_term(Apply_Selector, head, list_five);

  solver->push();
  solver->assert_formula(
      solver->make_term(Equal, selected_head, solver->make_term(5, int_sort)));
  solver->assert_formula(solver->make_term(Apply_Tester, is_nil, nil_term));
  solver->assert_formula(solver->make_term(Apply_Tester, is_cons, list_five));
  assert(solver->check_sat().is_sat());
  solver->pop();
}

void test_quantifiers(const SmtSolver & solver)
{
  Sort bool_sort = solver->make_sort(BOOL);
  Term x = solver->make_symbol("qx", bool_sort);
  Term y = solver->make_symbol("qy", bool_sort);
  Term implication = solver->make_term(Implies, x, y);
  Term forall_term = solver->make_term(Forall, TermVec{ x, implication });
  Term exists_term = solver->make_term(Exists, TermVec{ y, implication });

  assert(forall_term->get_op() == Forall);
  assert(exists_term->get_op() == Exists);
  assert(forall_term->get_sort() == bool_sort);
  assert(exists_term->get_sort() == bool_sort);
}

}  // namespace

int main()
{
  SmtSolver solver = Z3SolverFactory::create(false);

  test_linear_arithmetic(solver);
  test_bv_literals(solver);
  test_function_application(solver);
  test_datatypes(solver);
  test_quantifiers(solver);

  return 0;
}
