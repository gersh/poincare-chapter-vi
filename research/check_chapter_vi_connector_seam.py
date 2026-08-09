#!/usr/bin/env python3
"""Independent interval check for the homogeneous D-connector seam argument.

This is deliberately not a LeanCompCert client.  It transcribes the mathematical
expressions in ``ChapterVIDHomogeneousDerivative.lean`` into small rectangular
complex intervals and evaluates them with outward-rounded IEEE-754 endpoints.

The check is less formal than the Lean development: it assumes correctly-rounded
binary64 arithmetic for +, -, *, and /, and it does not produce a kernel proof.
Its purpose is to test the mathematical reduction independently and to expose the
actual margins before investing further in formal certificate plumbing.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from dataclasses import dataclass
from typing import Any, Iterable


NEG_INF = -math.inf
POS_INF = math.inf
PRECISION = 20
SCALE = 2**PRECISION
CELL_COUNT = 160
CELL_WIDTH = 1671


def down(value: float) -> float:
    return math.nextafter(value, NEG_INF)


def up(value: float) -> float:
    return math.nextafter(value, POS_INF)


@dataclass(frozen=True)
class Interval:
    lo: float
    hi: float

    def __post_init__(self) -> None:
        if math.isnan(self.lo) or math.isnan(self.hi) or self.lo > self.hi:
            raise ValueError(f"invalid interval [{self.lo}, {self.hi}]")

    @staticmethod
    def point(value: float | int) -> "Interval":
        value = float(value)
        return Interval(value, value)

    def __add__(self, other: RealLike) -> "Interval":
        if isinstance(other, ComplexBox):
            return NotImplemented
        other = interval(other)
        return Interval(down(self.lo + other.lo), up(self.hi + other.hi))

    __radd__ = __add__

    def __neg__(self) -> "Interval":
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other: RealLike) -> "Interval":
        if isinstance(other, ComplexBox):
            return NotImplemented
        return self + (-interval(other))

    def __rsub__(self, other: RealLike) -> "Interval":
        return interval(other) - self

    def __mul__(self, other: RealLike) -> "Interval":
        if isinstance(other, ComplexBox):
            return NotImplemented
        other = interval(other)
        candidates = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(down(min(candidates)), up(max(candidates)))

    __rmul__ = __mul__

    def reciprocal(self) -> "Interval":
        if self.lo <= 0.0 <= self.hi:
            raise ZeroDivisionError(f"interval contains zero: {self}")
        candidates = (1.0 / self.lo, 1.0 / self.hi)
        return Interval(down(min(candidates)), up(max(candidates)))

    def __truediv__(self, other: RealLike) -> "Interval":
        if isinstance(other, ComplexBox):
            return NotImplemented
        return self * interval(other).reciprocal()

    def __pow__(self, exponent: int) -> "Interval":
        if exponent < 0:
            return (self.reciprocal()) ** (-exponent)
        result = Interval.point(1)
        # Treat repeated occurrences as independent.  This is sometimes wider
        # than the optimal interval power, but is always a safe enclosure.
        for _ in range(exponent):
            result = result * self
        return result

    def contains(self, value: float) -> bool:
        return self.lo <= value <= self.hi

    def contains_interval(self, other: "Interval") -> bool:
        return self.lo <= other.lo and other.hi <= self.hi

    def as_list(self) -> list[float]:
        return [self.lo, self.hi]


RealLike = Interval | float | int


def interval(value: RealLike) -> Interval:
    return value if isinstance(value, Interval) else Interval.point(value)


@dataclass(frozen=True)
class ComplexBox:
    re: Interval
    im: Interval

    @staticmethod
    def point(re: float | int, im: float | int = 0) -> "ComplexBox":
        return ComplexBox(Interval.point(re), Interval.point(im))

    def __add__(self, other: ComplexLike) -> "ComplexBox":
        other = complex_box(other)
        return ComplexBox(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self) -> "ComplexBox":
        return ComplexBox(-self.re, -self.im)

    def __sub__(self, other: ComplexLike) -> "ComplexBox":
        return self + (-complex_box(other))

    def __rsub__(self, other: ComplexLike) -> "ComplexBox":
        return complex_box(other) - self

    def __mul__(self, other: ComplexLike) -> "ComplexBox":
        other = complex_box(other)
        return ComplexBox(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    __rmul__ = __mul__

    def reciprocal(self) -> "ComplexBox":
        denominator = self.re**2 + self.im**2
        return ComplexBox(self.re / denominator, -self.im / denominator)

    def __truediv__(self, other: ComplexLike) -> "ComplexBox":
        return self * complex_box(other).reciprocal()

    def __pow__(self, exponent: int) -> "ComplexBox":
        if exponent < 0:
            return (self.reciprocal()) ** (-exponent)
        result = ComplexBox.point(1)
        for _ in range(exponent):
            result = result * self
        return result

    def as_dict(self) -> dict[str, list[float]]:
        return {"re": self.re.as_list(), "im": self.im.as_list()}


ComplexLike = ComplexBox | Interval | float | int


def complex_box(value: ComplexLike) -> ComplexBox:
    if isinstance(value, ComplexBox):
        return value
    return ComplexBox(interval(value), Interval.point(0))


def norm_upper(value: ComplexBox) -> float:
    """A rounded-up Euclidean-norm bound for a complex rectangle."""

    real = max(abs(value.re.lo), abs(value.re.hi))
    imag = max(abs(value.im.lo), abs(value.im.hi))
    return up(math.sqrt(up(up(real * real) + up(imag * imag))))


def dyadic_interval(lower: int, upper: int) -> Interval:
    return Interval(lower / SCALE, upper / SCALE)


def rational_point(numerator: int, denominator: int) -> Interval:
    """An outward binary64 enclosure of an exact rational number."""

    value = numerator / denominator
    return Interval(down(value), up(value))


def dyadic_box(
    real_lower: int,
    real_upper: int,
    imag_lower: int,
    imag_upper: int,
) -> ComplexBox:
    return ComplexBox(
        dyadic_interval(real_lower, real_upper),
        dyadic_interval(imag_lower, imag_upper),
    )


# Primitive boxes.  These are the same mathematical enclosures used by the
# homogeneous Lean campaign, but the calculations below are independent.
COLLISION = dyadic_box(-314053, -314047, 0, 0)
Y_BASE = dyadic_box(-28312, -25000, 0, 0)
NORMALIZED_ENDPOINT = dyadic_box(-1024, 1024, -158311, -130048)
UNIT_SQUARE = ComplexBox(Interval(-1.0, 1.0), Interval(-1.0, 1.0))
LENGTH = dyadic_interval(0, 1)
COEFFICIENT_100 = dyadic_interval(3494, 3495)
COEFFICIENT_200 = dyadic_interval(20969, 20970)
INVERSE_10001 = dyadic_interval(104, 105)


def polynomial(x: Interval) -> Interval:
    """2500 x^3 + 500025 x^2 + 12501 x - 25, in Horner form."""

    return ((2500 * x + 500025) * x + 12501) * x - 25


def polynomial_derivative(x: Interval) -> Interval:
    return (7500 * x + 1000050) * x + 12501


def validate_primitive_boxes() -> dict[str, Any]:
    """Check the elementary real-algebraic enclosures used by the scan."""

    x_left = rational_point(-26865395705, 10**12)
    x_right = rational_point(-26865395704, 10**12)
    x_box = Interval(x_left.lo, x_right.hi)
    p_left = polynomial(x_left)
    p_right = polynomial(x_right)
    derivative = polynomial_derivative(x_box)
    if not (p_left.lo > 0 and p_right.hi < 0 and derivative.hi < 0):
        raise AssertionError("the stated cubic root bracket was not verified")

    # The negative real cube root of x lies in COLLISION.re.
    collision_cube = COLLISION.re**3
    if not collision_cube.contains_interval(x_box):
        raise AssertionError("collision cube-root box does not cover the cubic root")

    one_hundredth = rational_point(1, 100)
    y_from_x = (x_box - one_hundredth) ** 2 / (
        2 * (1 + one_hundredth**2) * x_box
    )
    if not Y_BASE.re.contains_interval(y_from_x):
        raise AssertionError("Y(D) box does not cover the value derived from x")

    exact_constants = {
        "100/30003": (COEFFICIENT_100, rational_point(100, 30003)),
        "200/10001": (COEFFICIENT_200, rational_point(200, 10001)),
        "1/10001": (INVERSE_10001, rational_point(1, 10001)),
    }
    for name, (box, value) in exact_constants.items():
        if not box.contains_interval(value):
            raise AssertionError(f"{name} is outside its dyadic enclosure")

    return {
        "root_interval": x_box.as_list(),
        "polynomial_at_left": p_left.as_list(),
        "polynomial_at_right": p_right.as_list(),
        "polynomial_derivative": derivative.as_list(),
        "collision_cube": collision_cube.as_list(),
        "y_from_root": y_from_x.as_list(),
    }


def argument_coefficient(u: ComplexBox) -> ComplexBox:
    d = COLLISION
    return (
        -COEFFICIENT_100
        * (u**2 + u * d + d**2)
        * (1 + u.reciprocal() ** 3 * d.reciprocal() ** 3)
    )


def multiplier_coefficient(u: ComplexBox) -> ComplexBox:
    d = COLLISION
    return (
        -2 * Y_BASE * d.reciprocal()
        + COEFFICIENT_200
        * Y_BASE
        * (d.reciprocal() * (u.reciprocal() ** 3 + u**3))
    )


def laurent_coefficient_difference(u: ComplexBox) -> ComplexBox:
    d = COLLISION
    inverse_two_difference = (
        -(u + d) * u.reciprocal() ** 2 * d.reciprocal() ** 2
    )
    inverse_four_difference = (
        -(u**3 + u**2 * d + u * d**2 + d**3)
        * u.reciprocal() ** 4
        * d.reciprocal() ** 4
    )
    power_term = d.reciprocal() ** 4 * (
        u.reciprocal() ** 2 + d**2 * u.reciprocal() ** 4
    )
    power_term_difference = d.reciprocal() ** 4 * (
        inverse_two_difference + d**2 * inverse_four_difference
    )
    return INVERSE_10001 * (
        (30000 + 3 * power_term) + 2 * d * (3 * power_term_difference)
    )


def power_shape_coefficient_difference(u: ComplexBox) -> ComplexBox:
    d = COLLISION
    quadratic = u**2 + u * d + d**2
    quadratic_difference = u + 2 * d
    inverse_cube_difference = (
        -quadratic * u.reciprocal() ** 3 * d.reciprocal() ** 3
    )
    inverse_factor = 1 - u.reciprocal() ** 3 * d.reciprocal() ** 3
    inverse_factor_difference = -(d.reciprocal() ** 3) * inverse_cube_difference
    return d.reciprocal() * (
        quadratic_difference * inverse_factor
        + 3 * d**2 * inverse_factor_difference
    )


def argument_coefficient_difference(u: ComplexBox) -> ComplexBox:
    d = COLLISION
    quadratic = u**2 + u * d + d**2
    quadratic_difference = u + 2 * d
    inverse_cube_difference = (
        -quadratic * u.reciprocal() ** 3 * d.reciprocal() ** 3
    )
    inverse_factor = 1 + u.reciprocal() ** 3 * d.reciprocal() ** 3
    inverse_factor_difference = d.reciprocal() ** 3 * inverse_cube_difference
    return -COEFFICIENT_100 * (
        quadratic_difference * inverse_factor
        + 3 * d**2 * inverse_factor_difference
    )


def multiplier_coefficient_difference(u: ComplexBox) -> ComplexBox:
    d = COLLISION
    quadratic = u**2 + u * d + d**2
    inverse_cube_difference = (
        -quadratic * u.reciprocal() ** 3 * d.reciprocal() ** 3
    )
    return (
        COEFFICIENT_200
        * Y_BASE
        * d.reciprocal()
        * (inverse_cube_difference + quadratic)
    )


def linear_coefficient_at_collision() -> ComplexBox:
    """The coefficient A=f''(D), evaluated from its removable formula."""

    d = COLLISION
    laurent = (
        INVERSE_10001
        * (d + d)
        * (30000 + 3 * (d**2 + d**2) / (d**4 * d**4))
    )
    power_shape = (
        (d**2 + d * d + d**2)
        * d.reciprocal()
        * (1 - d.reciprocal() ** 3 * d.reciprocal() ** 3)
    )
    coordinate = laurent + COEFFICIENT_200 * Y_BASE * power_shape
    return coordinate + argument_coefficient(d) * multiplier_coefficient(d)


def quadratic_coefficient(u: ComplexBox, exponential_remainder: ComplexBox) -> ComplexBox:
    d = COLLISION
    coordinate_difference = (
        laurent_coefficient_difference(u)
        + COEFFICIENT_200 * Y_BASE * power_shape_coefficient_difference(u)
    )
    argument_at_base = (
        -COEFFICIENT_100
        * (d**2 + d * d + d**2)
        * (1 + d.reciprocal() ** 3 * d.reciprocal() ** 3)
    )
    linear_difference = (
        coordinate_difference
        + argument_coefficient_difference(u) * multiplier_coefficient(u)
        + argument_at_base * multiplier_coefficient_difference(u)
    )
    return (
        linear_difference
        + argument_coefficient(u) ** 2
        * exponential_remainder
        * multiplier_coefficient(u)
    )


def parameter_coefficient(u: ComplexBox, exponential_remainder: ComplexBox) -> ComplexBox:
    argument = (u - COLLISION) * argument_coefficient(u)
    return (
        1 + argument + argument**2 * exponential_remainder
    ) * multiplier_coefficient(u)


def collapsed_direction(side: str) -> ComplexBox:
    if side == "initial":
        return -COLLISION * ComplexBox.point(1, 1)
    if side == "final":
        return -COLLISION * ComplexBox.point(1, -1)
    raise ValueError(side)


def homogeneous_direction(side: str) -> ComplexBox:
    sign = -1 if side == "initial" else 1
    return (
        collapsed_direction(side)
        + complex_box(LENGTH**2) * UNIT_SQUARE
        - sign * complex_box(LENGTH) * NORMALIZED_ENDPOINT
    )


def distance_cell(index: int) -> Interval:
    if not 0 <= index < CELL_COUNT:
        raise ValueError(index)
    return dyadic_interval(index * CELL_WIDTH, (index + 1) * CELL_WIDTH)


def scan_side(side: str) -> dict[str, Any]:
    sign = -1 if side == "initial" else 1
    base = collapsed_direction(side)
    direction = homogeneous_direction(side)
    linear = linear_coefficient_at_collision()

    endpoint_min = (POS_INF, -1)
    endpoint_max = (NEG_INF, -1)
    distance_min = (POS_INF, -1)
    distance_max = (NEG_INF, -1)
    coordinate_real = Interval(POS_INF, POS_INF)
    coordinate_imag = Interval(POS_INF, POS_INF)
    maximum_argument_norm = (NEG_INF, -1)
    rows: list[dict[str, float | int]] = []
    first_coordinate = True

    for index in range(CELL_COUNT):
        distance = distance_cell(index)
        coordinate = (
            COLLISION
            + sign * complex_box(LENGTH) * NORMALIZED_ENDPOINT
            + complex_box(distance) * direction
        )
        if first_coordinate:
            coordinate_real = coordinate.re
            coordinate_imag = coordinate.im
            first_coordinate = False
        else:
            coordinate_real = Interval(
                min(coordinate_real.lo, coordinate.re.lo),
                max(coordinate_real.hi, coordinate.re.hi),
            )
            coordinate_imag = Interval(
                min(coordinate_imag.lo, coordinate.im.lo),
                max(coordinate_imag.hi, coordinate.im.hi),
            )

        argument = (coordinate - COLLISION) * argument_coefficient(coordinate)
        argument_norm = norm_upper(argument)
        if argument_norm > maximum_argument_norm[0]:
            maximum_argument_norm = (argument_norm, index)
        if argument_norm > 1:
            raise AssertionError(
                f"exponential argument escaped the unit disk for {side} "
                f"cell {index}: norm <= {argument_norm}"
            )

        # For |a| <= 1, the exact exponential second-remainder factor
        # E(a)=(exp(a)-1-a)/a^2 has norm at most one, hence is in this square.
        remainder = UNIT_SQUARE
        quadratic = quadratic_coefficient(coordinate, remainder)
        parameter = parameter_coefficient(coordinate, remainder)

        endpoint = (
            linear * sign * NORMALIZED_ENDPOINT * direction
            + distance
            * linear
            * (complex_box(LENGTH) * UNIT_SQUARE - sign * NORMALIZED_ENDPOINT)
            * (direction + base)
            + (
                complex_box(LENGTH) * NORMALIZED_ENDPOINT**2
                + 2
                * sign
                * complex_box(distance)
                * NORMALIZED_ENDPOINT
                * direction
            )
            * quadratic
            * direction
            + complex_box(LENGTH) * UNIT_SQUARE * parameter * direction
        )
        distance_coefficient = direction**3 * quadratic

        if endpoint.re.lo < endpoint_min[0]:
            endpoint_min = (endpoint.re.lo, index)
        if endpoint.re.hi > endpoint_max[0]:
            endpoint_max = (endpoint.re.hi, index)
        if distance_coefficient.re.lo < distance_min[0]:
            distance_min = (distance_coefficient.re.lo, index)
        if distance_coefficient.re.hi > distance_max[0]:
            distance_max = (distance_coefficient.re.hi, index)

        if endpoint.re.lo <= 0 or distance_coefficient.re.lo <= 0:
            raise AssertionError(
                f"positivity failed for {side} cell {index}: "
                f"endpoint={endpoint.re}, distance={distance_coefficient.re}"
            )

        rows.append(
            {
                "cell": index,
                "delta_lower": distance.lo,
                "delta_upper": distance.hi,
                "endpoint_real_lower": endpoint.re.lo,
                "distance_real_lower": distance_coefficient.re.lo,
                "argument_norm_upper": argument_norm,
            }
        )

    return {
        "side": side,
        "cells": CELL_COUNT,
        "endpoint_real_lower": endpoint_min[0],
        "endpoint_real_lower_cell": endpoint_min[1],
        "endpoint_real_upper": endpoint_max[0],
        "endpoint_real_upper_cell": endpoint_max[1],
        "distance_real_lower": distance_min[0],
        "distance_real_lower_cell": distance_min[1],
        "distance_real_upper": distance_max[0],
        "distance_real_upper_cell": distance_max[1],
        "coordinate_real_envelope": coordinate_real.as_list(),
        "coordinate_imag_envelope": coordinate_imag.as_list(),
        "direction": direction.as_dict(),
        "maximum_argument_norm": maximum_argument_norm[0],
        "maximum_argument_norm_cell": maximum_argument_norm[1],
        "rows": rows,
    }


def run_check() -> dict[str, Any]:
    collar_upper = 261 / 1024
    covered_upper = CELL_COUNT * CELL_WIDTH / SCALE
    if covered_upper < collar_upper:
        raise AssertionError(
            f"cell table ends at {covered_upper}, below collar endpoint {collar_upper}"
        )
    primitives = validate_primitive_boxes()
    linear = linear_coefficient_at_collision()
    sides = [scan_side("initial"), scan_side("final")]
    comparison_keys = (
        "delta_lower",
        "delta_upper",
        "endpoint_real_lower",
        "distance_real_lower",
        "argument_norm_upper",
    )
    for initial, final in zip(sides[0]["rows"], sides[1]["rows"], strict=True):
        if any(initial[key] != final[key] for key in comparison_keys):
            raise AssertionError(
                f"initial/final symmetry failed in cell {initial['cell']}"
            )
    return {
        "method": "outward-rounded binary64 rectangular interval arithmetic",
        "precision": PRECISION,
        "cells_per_side": CELL_COUNT,
        "cell_width_raw": CELL_WIDTH,
        "covered_distance_upper": covered_upper,
        "collar_distance_upper": collar_upper,
        "side_symmetry_verified": True,
        "primitive_checks": primitives,
        "linear_coefficient": linear.as_dict(),
        "sides": sides,
        "result": "PASS",
    }


def print_human(report: dict[str, Any]) -> None:
    print("Chapter VI homogeneous connector seam check: PASS")
    print(f"  cells checked: {2 * report['cells_per_side']}")
    print(
        "  table: "
        f"{report['cells_per_side']} rows of width "
        f"{report['cell_width_raw']}/2^{report['precision']} cover both sides by symmetry"
    )
    linear = report["linear_coefficient"]
    print(
        "  A=f''(D): "
        f"Re in [{linear['re'][0]:.12g}, {linear['re'][1]:.12g}], "
        f"Im in [{linear['im'][0]:.3g}, {linear['im'][1]:.3g}]"
    )
    for side in report["sides"]:
        print(f"  {side['side']}:")
        print(
            "    Re X >= "
            f"{side['endpoint_real_lower']:.12g} "
            f"(cell {side['endpoint_real_lower_cell']})"
        )
        print(
            "    Re Y >= "
            f"{side['distance_real_lower']:.12g} "
            f"(cell {side['distance_real_lower_cell']})"
        )
        print(
            "    u envelope: Re "
            f"{side['coordinate_real_envelope']}, "
            f"Im {side['coordinate_imag_envelope']}"
        )
        print(
            "    max |exponential argument| <= "
            f"{side['maximum_argument_norm']:.12g} "
            f"(cell {side['maximum_argument_norm_cell']})"
        )


def print_csv(report: dict[str, Any]) -> None:
    """Print the one-side table; the verified conjugation symmetry covers both sides."""

    fieldnames = [
        "cell",
        "delta_lower",
        "delta_upper",
        "endpoint_real_lower",
        "distance_real_lower",
        "argument_norm_upper",
    ]
    writer = csv.DictWriter(sys.stdout, fieldnames=fieldnames, lineterminator="\n")
    writer.writeheader()
    writer.writerows(report["sides"][0]["rows"])


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit the complete report as JSON")
    parser.add_argument(
        "--csv",
        action="store_true",
        help="emit the 160-row table (valid for both sides by checked symmetry)",
    )
    args = parser.parse_args(argv)
    report = run_check()
    if args.csv:
        print_csv(report)
    elif args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print_human(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
