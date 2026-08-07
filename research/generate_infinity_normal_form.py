#!/usr/bin/env python3
"""Generate exact certificate data for the Section 103 infinity normal forms.

The script is deliberately outside the trusted proof.  It solves finite linear systems over
``QQ(i)`` to find identities ``H h = A f + B g``.  Here ``f,g`` are a chart pair, ``h`` is one
of the three triangular generators, and ``H(0) != 0``.  It also divides ``f,g`` by the triangular
basis.  The generated identities are intended to be checked independently in LeanCompCert.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp
from sympy.polys.domains import QQ_I
from sympy.polys.matrices import DomainMatrix


SEXTIC = [
    [(0, 0), (0, 0), (4563, 0), (0, 0), (0, 0)],
    [(0, 0), (21320, -33280), (-56420, 20800), (46280, -20800), (0, 0)],
    [(7500, 0), (-118560, 7488), (308826, 0), (-118560, -7488), (7500, 0)],
    [(0, 0), (46280, 20800), (-56420, -20800), (21320, 33280), (0, 0)],
    [(0, 0), (0, 0), (4563, 0), (0, 0), (0, 0)],
]

REDUCED = [
    [(0, 0), (90285, -99840), (-136890, 0), (-112515, 62400), (0, 0)],
    [(106500, -96000), (-1051430, 914464), (1041300, -468000),
     (-38470, 186464), (88500, -60000)],
    [(-150000, 0), (1388400, -112320), (0, 0), (-1388400, -112320),
     (150000, 0)],
    [(-88500, -60000), (38470, 186464), (-1041300, -468000),
     (1051430, 914464), (-106500, -96000)],
    [(0, 0), (112515, 62400), (136890, 0), (-90285, -99840), (0, 0)],
]

NORMAL_FORM = {
    "x": (
        sp.Rational(19269075500, 1986406227) + sp.Rational(8990080000, 1986406227) * sp.I,
        sp.Rational(1609189401043610000, 7782662127543147)
        + sp.Rational(39107128473251264000, 303523822974182733) * sp.I,
        -sp.Rational(4684300, 5659277) - sp.Rational(420000, 5659277) * sp.I,
        -sp.Rational(1120885285578800, 96082248488187)
        + sp.Rational(75605916903360, 32027416162729) * sp.I,
    ),
    "y": (
        sp.Rational(1581838141, 190537500) - sp.Rational(25348648, 9526875) * sp.I,
        sp.Rational(40224953174838601, 181522694531250)
        - sp.Rational(24501487240547252, 453806736328125) * sp.I,
        -sp.Rational(608959, 508100) - sp.Rational(546, 5081) * sp.I,
        -sp.Rational(5598740861831, 387248415000)
        - sp.Rational(226996761992, 80676753125) * sp.I,
    ),
}


def gaussian(pair: tuple[int, int]):
    return sp.Integer(pair[0]) + sp.Integer(pair[1]) * sp.I


def chart_polynomial(chart: str, coefficients, degree: int, y, z):
    result = 0
    for a in range(5):
        for b in range(5):
            y_degree = b if chart == "x" else a
            z_degree = max(0, degree - a - b)
            result += gaussian(coefficients[a][b]) * y**y_degree * z**z_degree
    return sp.expand(result)


def coefficient_dict(expression, y, z):
    return dict(sp.Poly(sp.expand(expression), y, z, extension=sp.I).terms())


def solve_membership(f, g, target, y, z, max_y=3, max_z=26):
    """Solve ``A*f + B*g = target`` with the displayed rectangular degree bound."""
    labels = []
    columns = []
    for generator_name, generator in (("f", f), ("g", g)):
        for y_degree in range(max_y + 1):
            for z_degree in range(max_z + 1):
                labels.append((generator_name, y_degree, z_degree))
                columns.append(coefficient_dict(y**y_degree * z**z_degree * generator, y, z))
    labels.append(("target", 0, 0))
    columns.append(coefficient_dict(-target, y, z))
    monomials = sorted(set().union(*(column.keys() for column in columns)))
    rows = [[column.get(monomial, 0) for column in columns] for monomial in monomials]
    matrix = DomainMatrix.from_list_sympy(len(rows), len(columns), rows).convert_to(QQ_I)
    nullspace = matrix.nullspace(divide_last=True).to_Matrix().tolist()
    solution = next(row for row in nullspace if row[-1] != 0)
    solution = [sp.cancel(value / solution[-1]) for value in solution]
    a_polynomial = 0
    b_polynomial = 0
    for coefficient, (name, y_degree, z_degree) in zip(solution[:-1], labels[:-1]):
        term = coefficient * y**y_degree * z**z_degree
        if name == "f":
            a_polynomial += term
        else:
            b_polynomial += term
    a_polynomial = sp.expand(a_polynomial)
    b_polynomial = sp.expand(b_polynomial)
    assert sp.expand(a_polynomial * f + b_polynomial * g - target) == 0
    return a_polynomial, b_polynomial


def rational_pair(value):
    value = sp.expand_complex(value)
    real = sp.Rational(sp.re(value))
    imaginary = sp.Rational(sp.im(value))
    return [[int(real.p), int(real.q)], [int(imaginary.p), int(imaginary.q)]]


def polynomial_data(expression, y, z):
    return [
        {"y": int(monomial[0]), "z": int(monomial[1]), "coefficient": rational_pair(coefficient)}
        for monomial, coefficient in sp.Poly(expression, y, z, extension=sp.I).terms()
    ]


def lean_rational(value):
    numerator, denominator = value
    if denominator == 1:
        return str(numerator)
    return f"({numerator} / {denominator} : ℚ)"


def lean_coefficient(value):
    return f"⟨{lean_rational(value[0])}, {lean_rational(value[1])}⟩"


def lean_polynomial(name, terms):
    if not terms:
        return f"def {name} : Sparse := []\n"
    body = ",\n    ".join(
        f"⟨⟨{term['y']}, {term['z']}⟩, {lean_coefficient(term['coefficient'])}⟩"
        for term in terms
    )
    return f"def {name} : Sparse :=\n  [{body}]\n"


def render_lean(results):
    pieces = ["""/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import PoincareChapterVI.Section103.IntersectionResultant

/-! Automatically generated exact data for the Section 103 infinity normal-form certificates. -/

namespace PoincareChapterVI.InfinityNormalFormData

open PoincareChapterVI.Section103Source

abbrev QI := PoincareChapterVI.Section103Source.QI

structure Exp where
  y : ℕ
  z : ℕ
deriving DecidableEq, Ord

structure Term where
  exp : Exp
  coeff : QI
deriving DecidableEq

abbrev Sparse := List Term
"""]
    for result in results:
        prefix = result["chart"]
        for index, value in enumerate(result["normal_form"]):
            pieces.append(f"def {prefix}Coeff{index + 1} : QI := {lean_coefficient(value)}\n")
        for field in ("f", "g", "h1", "h2", "h3", "cofactor"):
            pieces.append(lean_polynomial(f"{prefix}{field.capitalize()}", result[field]))
        for index, witness in enumerate(result["localized_witnesses"], 1):
            pieces.append(lean_polynomial(f"{prefix}LocalizedLeft{index}", witness["left"]))
            pieces.append(lean_polynomial(f"{prefix}LocalizedRight{index}", witness["right"]))
        for chart_generator, witnesses in zip(("F", "G"), result["chart_witnesses"]):
            for index, witness in enumerate(witnesses, 1):
                pieces.append(lean_polynomial(f"{prefix}{chart_generator}Quotient{index}", witness))
    pieces.append("\nend PoincareChapterVI.InfinityNormalFormData\n")
    return "\n".join(pieces)


def generate_chart(chart: str):
    y, z = sp.symbols("y z")
    f = chart_polynomial(chart, SEXTIC, 6, y, z)
    g = chart_polynomial(chart, REDUCED, 7, y, z)
    resultant = sp.resultant(f, g, y)
    resultant_polynomial = sp.Poly(resultant, z, extension=sp.I)
    order = min(monomial[0] for monomial, _ in resultant_polynomial.terms())
    cofactor = sp.cancel(resultant / z**order)
    a, b, c, d = NORMAL_FORM[chart]
    triangular = [y**2 + a * z**4 + b * z**5,
                  y * z**2 + c * z**4 + d * z**5,
                  z**6]
    localized_witnesses = []
    for index, generator in enumerate(triangular):
        print(f"{chart}: solving localized witness {index + 1}/3", flush=True)
        left, right = solve_membership(f, g, sp.expand(cofactor * generator), y, z)
        localized_witnesses.append({"left": polynomial_data(left, y, z),
                                    "right": polynomial_data(right, y, z)})
    basis = sp.groebner(triangular, y, z, order="lex", extension=sp.I)
    chart_witnesses = []
    for generator in (f, g):
        quotients, remainder = basis.reduce(generator)
        assert remainder == 0
        chart_witnesses.append([polynomial_data(quotient, y, z) for quotient in quotients])
    return {
        "chart": chart,
        "resultant_order": order,
        "cofactor": polynomial_data(cofactor, y, z),
        "cofactor_at_zero": rational_pair(cofactor.subs(z, 0)),
        "normal_form": [rational_pair(value) for value in (a, b, c, d)],
        "f": polynomial_data(f, y, z),
        "g": polynomial_data(g, y, z),
        "h1": polynomial_data(triangular[0], y, z),
        "h2": polynomial_data(triangular[1], y, z),
        "h3": polynomial_data(triangular[2], y, z),
        "localized_witnesses": localized_witnesses,
        "chart_witnesses": chart_witnesses,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("chart", choices=("x", "y", "all"), default="all", nargs="?")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--lean-output", type=Path)
    args = parser.parse_args()
    charts = ("x", "y") if args.chart == "all" else (args.chart,)
    result = [generate_chart(chart) for chart in charts]
    serialized = json.dumps(result, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(serialized + "\n")
    else:
        print(serialized)
    if args.lean_output:
        args.lean_output.write_text(render_lean(result))


if __name__ == "__main__":
    main()
