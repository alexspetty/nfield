#!/bin/sh
# Copyright 2020-2026 Alexander S. Petty.
# SPDX-License-Identifier: Apache-2.0
# Author: Alexander S. Petty
set -eu

if [ "$#" -ne 0 ]; then
    printf '%s\n' 'usage: check-reset-forests.sh' >&2
    exit 2
fi

cd -- "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
lake build NField.Papers.SamplingDefectAndResetForests
lake env lean Checks/ResetForests.lean
