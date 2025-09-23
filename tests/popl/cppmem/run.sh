#!/usr/bin/env -S bash -euo pipefail

time ../../../cerbcore --impl gcc_4.9.0_x86_64-apple-darwin10.8.0 $@.core > $@.dot
dot -Tpdf $@.dot > $@.pdf
