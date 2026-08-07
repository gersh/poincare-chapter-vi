#!/usr/bin/env python3
"""Generate the exact affine-elimination certificate for Poincare's Section 103 curves.

This untrusted generator computes a lexicographic shape basis

    x + h(y),  y^2 q(y)

for the cleared affine sextic and septic.  It also produces polynomial membership witnesses in
both directions and a primitive Gaussian-integer multiple of the residual degree-24 polynomial.
Lean checks every generated identity independently.
"""

from __future__ import annotations

import argparse
import functools
import json
import math
from pathlib import Path

import sympy as sp

from generate_infinity_normal_form import (
    REDUCED,
    SEXTIC,
    gaussian,
    polynomial_data,
    rational_pair,
    solve_membership,
)


def affine_polynomial(coefficients, x, y):
    return sp.expand(
        sum(
            gaussian(coefficients[a][b]) * x**a * y**b
            for a in range(5)
            for b in range(5)
        )
    )


def primitive_gaussian_coefficients(polynomial: sp.Poly):
    coefficients = polynomial.all_coeffs()
    denominators = []
    for coefficient in coefficients:
        denominators.extend(
            [sp.denom(sp.re(coefficient)), sp.denom(sp.im(coefficient))]
        )
    common_denominator = int(sp.ilcm(*map(int, denominators)))
    raw = [
        (
            int(sp.re(coefficient) * common_denominator),
            int(sp.im(coefficient) * common_denominator),
        )
        for coefficient in coefficients
    ]
    content = functools.reduce(math.gcd, (abs(value) for pair in raw for value in pair))
    primitive = [(real // content, imaginary // content) for real, imaginary in raw]
    scale = common_denominator // content
    assert primitive[0] == (scale, 0)
    return list(reversed(primitive)), scale


def modular_squarefree_certificate(coefficients, prime=53, image_i=23):
    assert (image_i * image_i + 1) % prime == 0
    variable = sp.symbols("T")
    specialized = [
        (real + image_i * imaginary) % prime for real, imaginary in coefficients
    ]
    # The reduction must preserve the degree of the primitive Gaussian polynomial;
    # otherwise coprimality after specialization would not certify the leading term.
    assert specialized[-1] != 0
    polynomial = sp.Poly.from_list(list(reversed(specialized)), variable, modulus=prime)
    left, right, gcd = sp.gcdex(polynomial, polynomial.diff())
    inverse = pow(int(gcd.LC()), -1, prime)
    left = sp.Poly(left * inverse, variable, modulus=prime)
    right = sp.Poly(right * inverse, variable, modulus=prime)
    assert left * polynomial + right * polynomial.diff() == sp.Poly(1, variable, modulus=prime)

    def ascending(poly):
        return [int(poly.nth(index)) % prime for index in range(poly.degree() + 1)]

    return {
        "prime": prime,
        "image_i": image_i,
        "polynomial": specialized,
        "bezout_left": ascending(left),
        "bezout_right": ascending(right),
    }


def generate():
    x, y = sp.symbols("x y")
    sextic = affine_polynomial(SEXTIC, x, y)
    septic = affine_polynomial(REDUCED, x, y)
    basis = sp.groebner([sextic, septic], x, y, order="lex", extension=sp.I)
    assert len(basis.polys) == 2
    shape, eliminant = (sp.expand(polynomial.as_expr()) for polynomial in basis.polys)
    assert sp.Poly(shape, x, y, extension=sp.I).LC() == 1
    assert sp.degree(shape, x) == 1
    assert sp.expand(shape - x).subs(y, 0) == 0
    assert sp.expand(sp.cancel(eliminant / y**2) * y**2 - eliminant) == 0
    residual = sp.Poly(sp.cancel(eliminant / y**2), y, extension=sp.I)
    assert residual.degree() == 24
    assert residual.LC() == 1
    assert residual.TC() != 0

    print("solving shape membership witness", flush=True)
    shape_left, shape_right = solve_membership(
        sextic, septic, shape, x, y, max_y=3, max_z=26
    )
    print("solving eliminant membership witness", flush=True)
    eliminant_left, eliminant_right = solve_membership(
        sextic, septic, eliminant, x, y, max_y=3, max_z=26
    )
    sextic_quotients, sextic_remainder = basis.reduce(sextic)
    septic_quotients, septic_remainder = basis.reduce(septic)
    assert sextic_remainder == 0
    assert septic_remainder == 0

    gaussian_coefficients, gaussian_scale = primitive_gaussian_coefficients(residual)
    modular = modular_squarefree_certificate(gaussian_coefficients)
    return {
        "sextic": polynomial_data(sextic, x, y),
        "septic": polynomial_data(septic, x, y),
        "shape": polynomial_data(shape, x, y),
        "shape_tail": polynomial_data(shape - x, x, y),
        "eliminant": polynomial_data(eliminant, x, y),
        "residual": polynomial_data(residual.as_expr(), x, y),
        "shape_left": polynomial_data(shape_left, x, y),
        "shape_right": polynomial_data(shape_right, x, y),
        "eliminant_left": polynomial_data(eliminant_left, x, y),
        "eliminant_right": polynomial_data(eliminant_right, x, y),
        "sextic_quotient_shape": polynomial_data(sextic_quotients[0], x, y),
        "sextic_quotient_eliminant": polynomial_data(sextic_quotients[1], x, y),
        "septic_quotient_shape": polynomial_data(septic_quotients[0], x, y),
        "septic_quotient_eliminant": polynomial_data(septic_quotients[1], x, y),
        "gaussian_residual": [
            {"degree": degree, "coefficient": [real, imaginary]}
            for degree, (real, imaginary) in enumerate(gaussian_coefficients)
        ],
        "gaussian_scale": gaussian_scale,
        "modular": modular,
    }


def lean_rational(pair):
    numerator, denominator = pair
    return str(numerator) if denominator == 1 else f"({numerator} / {denominator} : ℚ)"


def lean_qi(value):
    return f"⟨{lean_rational(value[0])}, {lean_rational(value[1])}⟩"


def lean_sparse(name, terms):
    if not terms:
        return f"def {name} : Sparse := []\n"
    body = ",\n    ".join(
        f"⟨⟨{term['y']}, {term['z']}⟩, {lean_qi(term['coefficient'])}⟩"
        for term in terms
    )
    return f"def {name} : Sparse :=\n  [{body}]\n"


def lean_nat_list(name, values):
    return f"def {name} : List ℕ := [{', '.join(map(str, values))}]\n"


def render_lean(result):
    pieces = ["""/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.ReducedCurveSource

/-! Automatically generated exact data for the Section 103 affine elimination certificate. -/

namespace PoincareChapterVI.AffineEliminationData

abbrev QI := PoincareChapterVI.Section103Source.QI

structure Exp where
  x : ℕ
  y : ℕ
deriving DecidableEq

structure Term where
  exp : Exp
  coeff : QI
deriving DecidableEq

abbrev Sparse := List Term
"""]
    fields = [
        ("affineSextic", "sextic"),
        ("affineSeptic", "septic"),
        ("shapePolynomial", "shape"),
        ("shapeTail", "shape_tail"),
        ("eliminant", "eliminant"),
        ("residualPolynomial", "residual"),
        ("shapeLeft", "shape_left"),
        ("shapeRight", "shape_right"),
        ("eliminantLeft", "eliminant_left"),
        ("eliminantRight", "eliminant_right"),
        ("sexticQuotientShape", "sextic_quotient_shape"),
        ("sexticQuotientEliminant", "sextic_quotient_eliminant"),
        ("septicQuotientShape", "septic_quotient_shape"),
        ("septicQuotientEliminant", "septic_quotient_eliminant"),
    ]
    for lean_name, json_name in fields:
        pieces.append(lean_sparse(lean_name, result[json_name]))
    gaussian_body = ",\n    ".join(
        f"⟨{term['degree']}, ⟨{term['coefficient'][0]}, {term['coefficient'][1]}⟩⟩"
        for term in result["gaussian_residual"]
    )
    pieces.append(
        "def gaussianResidual : List (ℕ × GaussianInt) :=\n"
        f"  [{gaussian_body}]\n"
    )
    pieces.append(f"def gaussianScale : ℕ := {result['gaussian_scale']}\n")
    modular = result["modular"]
    pieces.append(f"def modularPrime : ℕ := {modular['prime']}\n")
    pieces.append(f"def modularImageI : ℕ := {modular['image_i']}\n")
    pieces.append(lean_nat_list("modularResidual", modular["polynomial"]))
    pieces.append(lean_nat_list("modularBezoutLeft", modular["bezout_left"]))
    pieces.append(lean_nat_list("modularBezoutRight", modular["bezout_right"]))
    pieces.append("\nend PoincareChapterVI.AffineEliminationData\n")
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
