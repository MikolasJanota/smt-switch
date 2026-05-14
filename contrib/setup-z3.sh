#!/bin/bash
git_tag=z3-4.16.0
github_owner=Z3Prover
cmake_options=(-DZ3_BUILD_LIBZ3_SHARED=Off)

# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$(realpath "$0")")/cmake-setup.sh"
