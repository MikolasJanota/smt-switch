#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include "smt.h"

#if BUILD_BITWUZLA
#include "bitwuzla_factory.h"
#include "bitwuzla/cpp/bitwuzla.h"
#endif

#if BUILD_BTOR
#include "boolector/boolector.h"
#include "boolector_factory.h"
#endif

#if BUILD_CVC5
#include "cvc5/cvc5.h"
#include "cvc5_factory.h"
#endif

#if BUILD_MSAT
#include "mathsat.h"
#include "msat_factory.h"
#endif

#if BUILD_YICES2
#include "yices.h"
#include "yices2_factory.h"
#endif

#if BUILD_Z3
#include "z3_factory.h"
#include "z3.h"
#endif

using namespace smt;

namespace {

struct BackendDemo
{
  std::string name;
  std::string version;
  SmtSolver solver;
};

void set_option_if_supported(const SmtSolver & solver,
                             const std::string & option,
                             const std::string & value)
{
  try
  {
    solver->set_opt(option, value);
  }
  catch (const std::exception &)
  {
  }
}

void configure_solver(const SmtSolver & solver)
{
  set_option_if_supported(solver, "incremental", "true");
  set_option_if_supported(solver, "produce-models", "true");

  try
  {
    solver->set_logic("QF_BV");
  }
  catch (const std::exception &)
  {
  }
}

void print_constraint(const std::string & description, const Term & term)
{
  std::cout << "    " << description << ": " << term << '\n';
}

void print_result(const SmtSolver & solver,
                  const Result & result,
                  const std::vector<std::pair<std::string, Term>> & values)
{
  std::cout << "    result: " << result << '\n';
  if (!result.is_sat())
  {
    return;
  }

  for (const auto & value : values)
  {
    std::cout << "    " << value.first << " = " << solver->get_value(value.second)
              << '\n';
  }
}

void solve_sat_case(const SmtSolver & solver,
                    const std::string & title,
                    const std::vector<std::pair<std::string, Term>> & constraints,
                    const std::vector<std::pair<std::string, Term>> & values)
{
  std::cout << "  " << title << '\n';
  solver->push();
  for (const auto & constraint : constraints)
  {
    print_constraint(constraint.first, constraint.second);
    solver->assert_formula(constraint.second);
  }
  print_result(solver, solver->check_sat(), values);
  solver->pop();
}

void run_bitvector_gallery(const BackendDemo & demo)
{
  const SmtSolver & solver = demo.solver;
  configure_solver(solver);

  Sort bv8 = solver->make_sort(BV, 8);
  Term one = solver->make_term(1, bv8);
  Term ten = solver->make_term(10, bv8);
  Term eleven = solver->make_term(11, bv8);
  Term low_mask = solver->make_term(0x0f, bv8);
  Term high_mask = solver->make_term(0xf0, bv8);
  Term low_nibble = solver->make_term(0x0b, bv8);
  Term high_nibble = solver->make_term(0xa0, bv8);
  Term aa = solver->make_term(0xaa, bv8);
  Term ff = solver->make_term(0xff, bv8);
  Term zero = solver->make_term(0, bv8);

  Term x = solver->make_symbol(demo.name + "_counter_x", bv8);
  Term y = solver->make_symbol(demo.name + "_counter_y", bv8);
  Term x_eq_10 = solver->make_term(Equal, x, ten);
  Term y_eq_x_plus_1 =
      solver->make_term(Equal, y, solver->make_term(BVAdd, x, one));
  solve_sat_case(solver,
                 "Counter check: x starts at 10 and y is the next byte",
                 { { "x == 10", x_eq_10 },
                   { "y == x + 1", y_eq_x_plus_1 } },
                 { { "x", x }, { "y", y } });

  Term key = solver->make_symbol(demo.name + "_key", bv8);
  Term low_bits =
      solver->make_term(Equal, solver->make_term(BVAnd, key, low_mask), low_nibble);
  Term high_bits = solver->make_term(
      Equal, solver->make_term(BVAnd, key, high_mask), high_nibble);
  solve_sat_case(solver,
                 "Masked-byte puzzle: recover a key from its nibbles",
                 { { "(key & 0x0f) == 0x0b", low_bits },
                   { "(key & 0xf0) == 0xa0", high_bits } },
                 { { "key", key } });

  Term a = solver->make_symbol(demo.name + "_xor_a", bv8);
  Term b = solver->make_symbol(demo.name + "_xor_b", bv8);
  Term a_eq_aa = solver->make_term(Equal, a, aa);
  Term xor_is_ff =
      solver->make_term(Equal, solver->make_term(BVXor, a, b), ff);
  solve_sat_case(solver,
                 "XOR partner: find b when a ^ b is all ones",
                 { { "a == 0xaa", a_eq_aa }, { "a ^ b == 0xff", xor_is_ff } },
                 { { "a", a }, { "b", b } });

  Term tick = solver->make_symbol(demo.name + "_tick", bv8);
  Term wraps_to_zero =
      solver->make_term(Equal, solver->make_term(BVAdd, tick, one), zero);
  solve_sat_case(solver,
                 "8-bit wraparound: which byte becomes zero after +1?",
                 { { "tick + 1 == 0", wraps_to_zero } },
                 { { "tick", tick } });

  Term impossible = solver->make_symbol(demo.name + "_impossible", bv8);
  Term impossible_eq_10 = solver->make_term(Equal, impossible, ten);
  Term impossible_eq_11 = solver->make_term(Equal, impossible, eleven);
  std::cout << "  Contradiction: one byte cannot be both 10 and 11\n";
  solver->push();
  print_constraint("z == 10", impossible_eq_10);
  solver->assert_formula(impossible_eq_10);
  print_constraint("z == 11", impossible_eq_11);
  solver->assert_formula(impossible_eq_11);
  print_result(solver, solver->check_sat(), {});
  solver->pop();
}

std::vector<BackendDemo> enabled_backends()
{
  std::vector<BackendDemo> backends;

#if BUILD_BITWUZLA
  backends.push_back({ "bitwuzla",
                       bitwuzla::version(),
                       BitwuzlaSolverFactory::create(false) });
#endif

#if BUILD_BTOR
  backends.push_back({ "boolector",
                       boolector_version(nullptr),
                       BoolectorSolverFactory::create(false) });
#endif

#if BUILD_CVC5
  {
    cvc5::Solver solver;
    backends.push_back(
        { "cvc5", solver.getVersion(), Cvc5SolverFactory::create(false) });
  }
#endif

#if BUILD_MSAT
  backends.push_back(
      { "mathsat", msat_get_version(), MsatSolverFactory::create(false) });
#endif

#if BUILD_YICES2
  backends.push_back(
      { "yices2", yices_version, Yices2SolverFactory::create(false) });
#endif

#if BUILD_Z3
  backends.push_back(
      { "z3", Z3_get_full_version(), Z3SolverFactory::create(false) });
#endif

  return backends;
}

}  // namespace

int main()
{
  std::vector<BackendDemo> backends = enabled_backends();
  if (backends.empty())
  {
    std::cout << "No backend solvers are enabled in this build.\n";
    return 0;
  }

  for (const BackendDemo & backend : backends)
  {
    std::cout << "\n=== " << backend.name << " ===\n";
    std::cout << "version: " << backend.version << '\n';
    run_bitvector_gallery(backend);
  }

  return 0;
}
