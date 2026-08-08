#!/usr/bin/env python3
"""Fixed-point feasibility scan for the dependency-preserving Chapter VI polar certificate.

This is not a proof artifact.  It uses the same outward-rounded interval operations intended for
the LeanCompCert table and reports whether the resulting rectangles have positive real product.
Lean will independently check every operation in any generated certificate.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import isqrt


Interval = tuple[int, int]
Rectangle = tuple[Interval, Interval]


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


class Fixed:
    def __init__(self, precision: int):
        self.p = precision
        self.scale = 1 << precision
        self.one = (self.scale, self.scale)

    def rational(self, value: Fraction) -> Interval:
        scaled = value * self.scale
        return floor_fraction(scaled), ceil_fraction(scaled)

    @staticmethod
    def add(x: Interval, y: Interval) -> Interval:
        return x[0] + y[0], x[1] + y[1]

    @staticmethod
    def neg(x: Interval) -> Interval:
        return -x[1], -x[0]

    def sub(self, x: Interval, y: Interval) -> Interval:
        return self.add(x, self.neg(y))

    def mul(self, x: Interval, y: Interval) -> Interval:
        corners = (x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1])
        return (
            floor_fraction(Fraction(min(corners), self.scale)),
            ceil_fraction(Fraction(max(corners), self.scale)),
        )

    def reciprocal(self, x: Interval) -> Interval:
        assert 0 < x[0]
        return (
            floor_fraction(Fraction(self.scale * self.scale, x[1])),
            ceil_fraction(Fraction(self.scale * self.scale, x[0])),
        )

    def integer_nth_root_floor(self, value: int, n: int) -> int:
        lo, hi = 0, 1
        while hi**n <= value:
            hi *= 2
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if mid**n <= value:
                lo = mid
            else:
                hi = mid
        return lo

    def root(self, x: Interval, n: int) -> Interval:
        lower_target = x[0] * self.scale ** (n - 1)
        upper_target = x[1] * self.scale ** (n - 1)
        lower = self.integer_nth_root_floor(lower_target, n)
        upper = self.integer_nth_root_floor(upper_target, n)
        if upper**n < upper_target:
            upper += 1
        def rounded_power(point: int) -> Interval:
            value = (point, point)
            square = self.mul(value, value)
            cube = self.mul(square, value)
            return cube if n == 3 else self.mul(cube, cube)

        while rounded_power(lower)[1] > x[0]:
            lower -= 1
        while rounded_power(upper)[0] < x[1]:
            upper += 1
        return lower, upper

    def cmul(self, x: Rectangle, y: Rectangle) -> Rectangle:
        rr = self.mul(x[0], y[0])
        ii = self.mul(x[1], y[1])
        ri = self.mul(x[0], y[1])
        ir = self.mul(x[1], y[0])
        return self.sub(rr, ii), self.add(ri, ir)

    def cadd(self, x: Rectangle, y: Rectangle) -> Rectangle:
        return self.add(x[0], y[0]), self.add(x[1], y[1])

    def csub(self, x: Rectangle, y: Rectangle) -> Rectangle:
        return self.sub(x[0], y[0]), self.sub(x[1], y[1])

    def cscale(self, r: Interval, z: Rectangle) -> Rectangle:
        return self.mul(r, z[0]), self.mul(r, z[1])

    @staticmethod
    def conj(z: Rectangle) -> Rectangle:
        return z[0], (-z[1][1], -z[1][0])

    def norm_upper(self, z: Rectangle) -> int:
        re = max(abs(z[0][0]), abs(z[0][1]))
        im = max(abs(z[1][0]), abs(z[1][1]))
        square = re * re + im * im
        root = isqrt(square)
        return root if root * root == square else root + 1

    @staticmethod
    def widen(z: Rectangle, error: int) -> Rectangle:
        return (z[0][0] - error, z[0][1] + error), (z[1][0] - error, z[1][1] + error)


def radial_data(fx: Fixed, i: int, cells: int, power: int) -> dict[str, Interval]:
    def node(j: int) -> Fraction:
        return 1 - Fraction(cells - min(j, cells), cells) ** power

    s = (floor_fraction(node(i) * fx.scale), ceil_fraction(node(i + 1) * fx.scale))
    qd = fx.rational(Fraction(8734, 10_000_000)), fx.rational(Fraction(8736, 10_000_000))
    qd = qd[0][0], qd[1][1]
    xabs_lo = fx.rational(Fraction(26_865_395, 1_000_000_000))[0]
    xabs_hi = fx.rational(Fraction(26_865_396, 1_000_000_000))[1]
    qd6 = fx.root(qd, 6)
    collision_radius = fx.root((xabs_lo, xabs_hi), 3)
    correction = fx.mul(collision_radius, fx.reciprocal(qd6))
    q = fx.add(fx.one, fx.mul(s, fx.sub(qd, fx.one)))
    zeta = fx.root(q, 3)
    q6 = fx.root(q, 6)
    correction_factor = fx.add(fx.one, fx.mul(s, fx.sub(correction, fx.one)))
    radius = fx.mul(q6, correction_factor)
    return {"input": s, "qCubeRoot": zeta, "qSixthRoot": q6, "radius": radius}


def radial_cell(fx: Fixed, i: int, cells: int, power: int) -> tuple[Interval, Interval]:
    data = radial_data(fx, i, cells, power)
    return data["qCubeRoot"], data["radius"]


def unit_cell(fx: Fixed, side: int, i: int, cells: int, power: int,
              symmetric: bool) -> Rectangle:
    def node(j: int) -> Fraction:
        if symmetric:
            j = min(j, cells)
            return Fraction(j**power, j**power + (cells - j)**power)
        return 1 - Fraction(cells - min(j, cells), cells) ** power

    t = (floor_fraction(node(i) * fx.scale), ceil_fraction(node(i + 1) * fx.scale))
    t2 = fx.mul(t, t)
    denominator_inv = fx.reciprocal(fx.add(fx.one, t2))
    re = fx.mul(fx.sub(fx.one, t2), denominator_inv)
    im = fx.mul(fx.mul(fx.rational(Fraction(2)), t), denominator_inv)
    return (re, im) if side == 0 else (im, fx.neg(re))


def radicand(fx: Fixed, zeta: Interval, radius: Interval, unit: Rectangle) -> Rectangle:
    unit2 = fx.cmul(unit, unit)
    unit3 = fx.cmul(unit2, unit)
    radius2 = fx.mul(radius, radius)
    radius3 = fx.mul(radius2, radius)
    radius_inv = fx.reciprocal(radius)
    radius3_inv = fx.reciprocal(radius3)
    zeta_inv = fx.reciprocal(zeta)
    u = fx.cscale(radius, unit)
    u_inv = fx.cscale(radius_inv, fx.conj(unit))
    u3 = fx.cscale(radius3, unit3)
    u3_inv = fx.cscale(radius3_inv, fx.conj(unit3))
    coefficient = fx.rational(Fraction(100, 30003))
    argument = fx.cscale(coefficient, fx.csub(u3_inv, u3))
    one_c = (fx.one, (0, 0))
    y_approx = fx.cscale(zeta, fx.cmul(u, fx.cadd(one_c, argument)))
    y_inv_approx = fx.cscale(zeta_inv, fx.cmul(u_inv, fx.csub(one_c, argument)))
    argument_norm = fx.mul(coefficient, fx.add(radius3_inv, radius3))
    argument_norm_sq = fx.mul(argument_norm, argument_norm)
    y_error = fx.mul(fx.mul(zeta, radius), argument_norm_sq)
    y_inv_error = fx.mul(fx.mul(zeta_inv, radius_inv), argument_norm_sq)
    y = fx.widen(y_approx, y_error[1])
    y_inv = fx.widen(y_inv_approx, y_inv_error[1])
    hundred = fx.rational(Fraction(100))
    ten_thousand = fx.rational(Fraction(10_000))
    minus_200 = fx.rational(Fraction(-200))
    inv_10001 = fx.rational(Fraction(1, 10001))
    two = fx.rational(Fraction(2))
    a_laurent = fx.cscale(inv_10001, fx.cadd(
        fx.cadd(fx.cscale(ten_thousand, u3), u3_inv), (minus_200, (0, 0))))
    b_laurent = fx.cscale(inv_10001, fx.cadd(
        fx.cadd(u3, fx.cscale(ten_thousand, u3_inv)), (minus_200, (0, 0))))
    a = fx.csub(a_laurent, fx.cscale(two, y))
    b = fx.csub(b_laurent, fx.cscale(two, y_inv))
    return fx.cmul(a, b)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--precision", type=int, default=30)
    parser.add_argument("--radial-cells", type=int, default=64)
    parser.add_argument("--radial-power", type=int, default=1)
    parser.add_argument("--angular-cells", type=int, default=64)
    parser.add_argument("--angular-power", type=int, default=1)
    parser.add_argument("--angular-symmetric", action="store_true")
    args = parser.parse_args()
    fx = Fixed(args.precision)
    minimum = None
    bad = 0
    for ri in range(args.radial_cells + 1):
        zeta, radius = radial_cell(fx, ri, args.radial_cells, args.radial_power)
        for side in range(2):
            for ti in range(args.angular_cells + 1):
                value = radicand(fx, zeta, radius,
                                  unit_cell(fx, side, ti, args.angular_cells,
                                            args.angular_power, args.angular_symmetric))
                lower = value[0][0]
                if lower <= 0:
                    bad += 1
                item = (lower, ri, side, ti, value)
                if minimum is None or item[0] < minimum[0]:
                    minimum = item
    assert minimum is not None
    lower, ri, side, ti, value = minimum
    print(f"minimum real lower = {lower / fx.scale:.12g}")
    print(f"bad cells = {bad}")
    print(f"at radial={ri}, side={'initial' if side == 0 else 'final'}, angular={ti}")
    print(f"rectangle = re[{value[0][0] / fx.scale:.12g}, {value[0][1] / fx.scale:.12g}] "
          f"im[{value[1][0] / fx.scale:.12g}, {value[1][1] / fx.scale:.12g}]")


if __name__ == "__main__":
    main()
