#!/usr/bin/env python3
"""Exploratory, non-rigorous scan of the concrete Chapter VI D outer arcs.

This script is not a proof artifact. It was used to reject a naive linear-radius contour and to
choose the explicit sixth-root radius with an affine endpoint correction formalized in
`ChapterVIDCertificateContour.lean`. The
eventual LeanCompCert certificate must use outward-rounded rational interval bounds and prove the
`ChapterVIDOuterArcNonvanishingCertificate` fields; floating-point samples here cannot discharge
that obligation.
"""

from __future__ import annotations

import argparse
import mpmath as mp


def d_polynomial(x: mp.mpf) -> mp.mpf:
    return 2500 * x**3 + 500025 * x**2 + 12501 * x - 25


def curve_three_y(x: mp.mpf) -> mp.mpf:
    tau = mp.mpf(1) / 100
    return (x - tau) ** 2 / (2 * (1 + tau**2) * x)


def curve_parameter(x: mp.mpf) -> mp.mpf:
    y = curve_three_y(x)
    return (-y) ** 3 / (-x) * mp.exp((-mp.mpf(100) / 10001) * (1 / x - x))


def root_to_original(u: mp.mpc) -> mp.mpc:
    return u * mp.exp((mp.mpf(100) / 30003) * (1 / u**3 - u**3))


def distance_plus(eccentricity: mp.mpf, complement: mp.mpf, x: mp.mpc) -> mp.mpc:
    return (x**2 + 1) - 2 * x * eccentricity + complement * (x**2 - 1)


def distance_minus(eccentricity: mp.mpf, complement: mp.mpf, x: mp.mpc) -> mp.mpc:
    return (x**2 + 1) - 2 * x * eccentricity - complement * (x**2 - 1)


def laurent_plus(eccentricity: mp.mpf, complement: mp.mpf, x: mp.mpc) -> mp.mpc:
    return distance_plus(eccentricity, complement, x) / (2 * x)


def laurent_minus(eccentricity: mp.mpf, complement: mp.mpf, x: mp.mpc) -> mp.mpc:
    return distance_minus(eccentricity, complement, x) / (2 * x)


def source_radicand(parameter: mp.mpf, radius: mp.mpf, unit: mp.mpc) -> mp.mpc:
    eccentricity = mp.mpf(200) / 10001
    complement = mp.mpf(9999) / 10001
    zeta = parameter ** (mp.mpf(1) / 3)
    u = radius * unit
    x = u**3
    y = zeta * root_to_original(u)
    plus = laurent_plus(eccentricity, complement, x) - 2 * laurent_plus(0, 1, y)
    minus = laurent_minus(eccentricity, complement, x) - 2 * laurent_minus(0, 1, y)
    return plus * minus


def scan(samples: int) -> None:
    x_d = mp.findroot(d_polynomial, (-mp.mpf(27) / 1000, -mp.mpf(26) / 1000))
    q_d = curve_parameter(x_d)
    r_d = (-x_d) ** (mp.mpf(1) / 3)
    sixth_correction = r_d / q_d ** (mp.mpf(1) / 6)

    def parameter(s: mp.mpf) -> mp.mpf:
        return 1 + (q_d - 1) * s

    def certificate_radius(s: mp.mpf) -> mp.mpf:
        q = parameter(s)
        return q ** (mp.mpf(1) / 6) * (1 + (sixth_correction - 1) * s)

    def exponential_correction_radius(s: mp.mpf) -> mp.mpf:
        q = parameter(s)
        return q ** (mp.mpf(1) / 6) * sixth_correction**s

    def linear_radius(s: mp.mpf) -> mp.mpf:
        return 1 + (r_d - 1) * s

    print(f"x_D = {mp.nstr(x_d, 30)}")
    print(f"q_D = {mp.nstr(q_d, 30)}")
    print(f"r_D = {mp.nstr(r_d, 30)}")
    print(f"sixth-root correction = {mp.nstr(sixth_correction, 30)}")

    for label, radius in (
        ("certificate affine-correction sixth-root radius", certificate_radius),
        ("earlier exponential-correction radius", exponential_correction_radius),
        ("unsafe linear radius", linear_radius),
    ):
        minimum = (mp.inf, mp.mpf(0), "", mp.mpf(0))
        for i in range(samples + 1):
            s = mp.mpf(i) / samples
            q = parameter(s)
            for side in ("initial", "final"):
                for j in range(samples + 1):
                    t = mp.mpf(j) / samples
                    quarter = ((1 - t**2) + 2j * t) / (1 + t**2)
                    unit = quarter if side == "initial" else -1j * quarter
                    value = abs(source_radicand(q, radius(s), unit))
                    if value < minimum[0]:
                        minimum = (value, s, side, t)
        print(
            f"{label}: sampled min |radicand| = {mp.nstr(minimum[0], 18)} "
            f"at s={mp.nstr(minimum[1], 10)}, side={minimum[2]}, "
            f"t={mp.nstr(minimum[3], 10)}"
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=100)
    parser.add_argument("--precision", type=int, default=50)
    args = parser.parse_args()
    if args.samples <= 0:
        parser.error("--samples must be positive")
    mp.mp.dps = args.precision
    scan(args.samples)


if __name__ == "__main__":
    main()
