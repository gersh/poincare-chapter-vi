#!/usr/bin/env python3
"""Generate the exact §103 infinitesimal-rotation restriction certificate.

The untrusted calculation reduces the three affine rotation derivatives modulo the radical
24-point shape ideal.  Lean independently checks the reduction identities and a modular rank-three
certificate for three coefficients of the resulting univariate remainders.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import json
import runpy
from pathlib import Path

import sympy as sp

from generate_infinity_normal_form import polynomial_data
from generate_affine_elimination import lean_sparse


def clear_gaussian(polynomial: sp.Expr, x, y):
    poly = sp.Poly(polynomial, x, y, extension=sp.I)
    denominators = []
    for coefficient in poly.coeffs():
        denominators += [sp.denom(sp.re(coefficient)), sp.denom(sp.im(coefficient))]
    scale = int(sp.ilcm(*map(int, denominators))) if denominators else 1
    cleared = sp.expand(scale * polynomial)
    for coefficient in sp.Poly(cleared, x, y, extension=sp.I).coeffs():
        assert sp.im(coefficient).is_Integer and sp.re(coefficient).is_Integer
    return scale, cleared


def modular_minor_certificate(matrix):
    for prime in list(sp.primerange(5, 300)):
        roots_i = [value for value in range(prime) if (value * value + 1) % prime == 0]
        for image_i in roots_i:
            reduced = sp.Matrix([
                [
                    (int(sp.re(value)) + image_i * int(sp.im(value))) % prime
                    for value in row
                ]
                for row in matrix.tolist()
            ])
            determinant = int(reduced.det()) % prime
            if determinant == 0:
                continue
            inverse = reduced.inv_mod(prime)
            assert (reduced * inverse).applyfunc(lambda value: int(value) % prime) == sp.eye(3)
            return {
                "prime": prime,
                "image_i": image_i,
                "matrix": [[int(value) % prime for value in row] for row in reduced.tolist()],
                "inverse": [[int(value) % prime for value in row] for row in inverse.tolist()],
            }
    raise RuntimeError("no modular rank certificate found")


def generate():
    with contextlib.redirect_stdout(io.StringIO()):
        audit = runpy.run_path("research/chapter_vi_section_103_audit.py")
    x, y, z = audit["x"], audit["y"], audit["z"]
    source_basis = sp.groebner(
        [audit["affine_p"].as_expr(), audit["affine_r"].as_expr()],
        x, y, order="lex", extension=sp.I,
    )
    source_shape, eliminant = [polynomial.as_expr() for polynomial in source_basis.polys]
    residual = sp.cancel(eliminant / y**2)
    radical_basis = sp.groebner(
        [source_shape, residual], x, y, order="lex", extension=sp.I
    )
    reduced_shape, reduced_residual = [polynomial.as_expr() for polynomial in radical_basis.polys]
    assert sp.simplify(reduced_residual - residual) == 0
    shape_quotient, shape_remainder = sp.div(
        sp.Poly(reduced_shape - source_shape, x, y, extension=sp.I),
        sp.Poly(residual, x, y, extension=sp.I),
    )
    assert shape_remainder.is_zero

    affine_directions = [
        sp.expand(direction.subs(z, 1)) for direction in audit["directional_derivatives"]
    ]
    direction_denominators = []
    for direction in affine_directions:
        for coefficient in sp.Poly(direction, x, y, extension=sp.I).coeffs():
            direction_denominators += [
                sp.denom(sp.re(coefficient)), sp.denom(sp.im(coefficient))
            ]
    direction_scale = int(sp.ilcm(*map(int, direction_denominators)))

    records = []
    gaussian_remainders = []
    remainder_scales = []
    for direction in affine_directions:
        cleared_direction = sp.expand(direction_scale * direction)
        quotients, remainder = radical_basis.reduce(cleared_direction)
        remainder_scale, gaussian_remainder = clear_gaussian(remainder, x, y)
        remainder_scales.append(remainder_scale)
        gaussian_remainders.append(gaussian_remainder)
        records.append({
            "direction": polynomial_data(cleared_direction, x, y),
            "shape_quotient": polynomial_data(
                sp.expand(remainder_scale * quotients[0]), x, y
            ),
            "residual_quotient": polynomial_data(
                sp.expand(remainder_scale * quotients[1]), x, y
            ),
            "remainder": polynomial_data(gaussian_remainder, x, y),
        })
        identity = sp.expand(
            remainder_scale * cleared_direction
            - remainder_scale * quotients[0] * reduced_shape
            - remainder_scale * quotients[1] * reduced_residual
            - gaussian_remainder
        )
        assert identity == 0

    minor = sp.Matrix([
        [sp.Poly(remainder, y, extension=sp.I).nth(degree) for remainder in gaussian_remainders]
        for degree in range(3)
    ])
    assert minor.det() != 0
    return {
        "direction_scale": direction_scale,
        "remainder_scales": remainder_scales,
        "reduced_shape": polynomial_data(reduced_shape, x, y),
        "shape_quotient": polynomial_data(shape_quotient.as_expr(), x, y),
        "records": records,
        "minor": [
            [
                [int(sp.re(value)), int(sp.im(value))]
                for value in row
            ]
            for row in minor.tolist()
        ],
        "modular": modular_minor_certificate(minor),
    }


def lean_nat_vector(name, values):
    return f"def {name} : Fin 3 → ℕ := ![{', '.join(map(str, values))}]\n"


def lean_gaussian_matrix(name, matrix):
    rows = []
    for row in matrix:
        rows.append(", ".join(f"⟨{real}, {imaginary}⟩" for real, imaginary in row))
    return f"def {name} : Matrix (Fin 3) (Fin 3) GaussianInt :=\n  !![" + ";\n    ".join(rows) + "]\n"


def lean_nat_matrix(name, matrix):
    rows = [", ".join(map(str, row)) for row in matrix]
    return f"def {name} : Matrix (Fin 3) (Fin 3) ℕ :=\n  !![" + ";\n    ".join(rows) + "]\n"


def render_lean(result):
    pieces = ["""/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.AffineEliminationData

/-! Automatically generated exact data for the §103 rotation-restriction certificate. -/

namespace PoincareChapterVI.RotationRestrictionData

open AffineEliminationData
"""]
    pieces.append(f"def directionScale : ℕ := {result['direction_scale']}\n")
    pieces.append(lean_nat_vector("remainderScale", result["remainder_scales"]))
    pieces.append(lean_sparse("reducedShape", result["reduced_shape"]))
    pieces.append(lean_sparse("reducedShapeQuotient", result["shape_quotient"]))
    for axis, record in enumerate(result["records"]):
        for lean_name, key in [
            (f"direction{axis}", "direction"),
            (f"directionShapeQuotient{axis}", "shape_quotient"),
            (f"directionResidualQuotient{axis}", "residual_quotient"),
            (f"directionRemainder{axis}", "remainder"),
        ]:
            pieces.append(lean_sparse(lean_name, record[key]))
    pieces.append(
        "def direction : Fin 3 → Sparse := "
        "![direction0, direction1, direction2]\n"
    )
    pieces.append(
        "def directionShapeQuotient : Fin 3 → Sparse := "
        "![directionShapeQuotient0, directionShapeQuotient1, directionShapeQuotient2]\n"
    )
    pieces.append(
        "def directionResidualQuotient : Fin 3 → Sparse := "
        "![directionResidualQuotient0, directionResidualQuotient1, directionResidualQuotient2]\n"
    )
    pieces.append(
        "def directionRemainder : Fin 3 → Sparse := "
        "![directionRemainder0, directionRemainder1, directionRemainder2]\n"
    )
    pieces.append(lean_gaussian_matrix("restrictionMinor", result["minor"]))
    modular = result["modular"]
    pieces.append(f"def modularPrime : ℕ := {modular['prime']}\n")
    pieces.append(f"def modularImageI : ℕ := {modular['image_i']}\n")
    pieces.append(lean_nat_matrix("modularMinor", modular["matrix"]))
    pieces.append(lean_nat_matrix("modularInverse", modular["inverse"]))
    pieces.append("\nend PoincareChapterVI.RotationRestrictionData\n")
    return "\n".join(pieces)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--lean-output", type=Path)
    args = parser.parse_args()
    result = generate()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    if args.lean_output:
        args.lean_output.write_text(render_lean(result))
    if not args.output and not args.lean_output:
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
