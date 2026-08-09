#!/usr/bin/env python3
"""Exploratory scan for the final 27/2744 radial-tail certificate.

This is deliberately not a proof artifact.  It identifies the two scale-normalized quantities
used by ``ChapterVIDRadialTailReduction.lean``:

* ``-d/ds Re R(s,h)`` on each of the six remaining cubic radial rows; and
* ``Re R(1,h) / h^2`` on the collision circle, with its removable value at ``h=0``.

Here ``h`` is angular distance from the negative-real pinch.  A trusted certificate must replace
the sampled minima below by outward-rounded interval enclosures checked in Lean/LeanCompCert.
"""

from __future__ import annotations

import argparse

import mpmath as mp

from chapter_vi_outer_arc_scan import curve_parameter, d_polynomial, source_radicand


def scan(samples: int, precision: int) -> None:
    mp.mp.dps = precision
    cells = 28
    node = lambda index: 1 - (mp.mpf(cells - index) / cells) ** 3

    x_d = mp.findroot(d_polynomial, (-mp.mpf(27) / 1000, -mp.mpf(26) / 1000))
    q_d = curve_parameter(x_d)
    r_d = (-x_d) ** (mp.mpf(1) / 3)
    correction = r_d / q_d ** (mp.mpf(1) / 6)

    def radicand(s: mp.mpf, h: mp.mpf) -> mp.mpc:
        parameter = 1 + (q_d - 1) * s
        radius = parameter ** (mp.mpf(1) / 6) * (1 + (correction - 1) * s)
        return source_radicand(parameter, radius, -mp.exp(1j * h))

    def negative_radial_derivative(s: mp.mpf, h: mp.mpf) -> mp.mpf:
        return -mp.diff(lambda parameter: mp.re(radicand(parameter, h)), s)

    print("row,s_lower,s_upper,sampled_min_negative_radial_derivative")
    for row in range(22, 28):
        lower = node(row)
        upper = node(row + 1)
        minimum = mp.inf
        for radial_index in range(samples + 1):
            s = lower + (upper - lower) * radial_index / samples
            for angular_index in range(samples + 1):
                h = (mp.pi / 2) * angular_index / samples
                minimum = min(minimum, negative_radial_derivative(s, h))
        print(
            f"{row},{mp.nstr(lower, 16)},{mp.nstr(upper, 16)},"
            f"{mp.nstr(minimum, 16)}"
        )

    endpoint_minimum = mp.inf
    endpoint_location = mp.mpf(0)
    endpoint_limit = mp.diff(lambda h: mp.re(radicand(1, h)), 0, 2) / 2
    for angular_index in range(1, 8 * samples + 1):
        h = (mp.pi / 2) * angular_index / (8 * samples)
        value = mp.re(radicand(1, h)) / h**2
        if value < endpoint_minimum:
            endpoint_minimum = value
            endpoint_location = h
    print(
        "endpoint,0,pi/2,"
        f"{mp.nstr(min(endpoint_limit, endpoint_minimum), 16)}"
    )
    print(f"endpoint_limit={mp.nstr(endpoint_limit, 16)}")
    print(f"endpoint_sample_location={mp.nstr(endpoint_location, 16)}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=64)
    parser.add_argument("--precision", type=int, default=50)
    args = parser.parse_args()
    if args.samples <= 0:
        parser.error("--samples must be positive")
    scan(args.samples, args.precision)


if __name__ == "__main__":
    main()
