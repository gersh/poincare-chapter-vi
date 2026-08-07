"""Exact-arithmetic audit of the projective calculation in Chapter VI, section 103.

This is a research script, not part of the trusted Lean proof.  It chooses two
genuine spatial Kepler ellipses with rational eccentricities, rational square
roots of ``1 - e^2``, and a rational relative rotation.  SymPy then constructs
Poincare's homogeneous polynomials P and R exactly over Q(i).

The output is intended to locate the finite certificates that must subsequently
be checked in Lean: coprimality, the two order-eight contributions at infinity,
and injectivity of the infinitesimal relative-rotation map.
"""

from __future__ import annotations

import sympy as sym


I = sym.I
x, y, z = sym.symbols("x y z")


def dot(left: sym.Matrix, right: sym.Matrix) -> sym.Expr:
    """Bilinear, rather than Hermitian, dot product used after complexification."""

    return sym.expand(left.dot(right))


eccentricity = sym.Rational(3, 5)
minor_axis_factor = sym.Rational(4, 5)
second_eccentricity = sym.Rational(5, 13)
second_minor_axis_factor = sym.Rational(12, 13)
semimajor_axis_ratio = sym.Rational(2)

# Rotation obtained from the rational quaternion (1, 2, 3, 4).
rotation = sym.Matrix(
    [
        [-sym.Rational(2, 3), sym.Rational(2, 15), sym.Rational(11, 15)],
        [sym.Rational(2, 3), -sym.Rational(1, 3), sym.Rational(2, 3)],
        [sym.Rational(1, 3), sym.Rational(14, 15), sym.Rational(2, 15)],
    ]
)
assert rotation.T * rotation == sym.eye(3)
assert rotation.det() == 1

first_major_axis = sym.Matrix([1, 0, 0])
first_minor_axis = sym.Matrix([0, 1, 0])
second_major_axis = rotation[:, 0]
second_minor_axis = rotation[:, 1]


def poincare_coefficients(
    second_major: sym.Matrix, second_minor: sym.Matrix
) -> tuple[sym.Matrix, sym.Matrix, sym.Matrix, sym.Matrix, sym.Matrix]:
    """Return A,B,C,D,E in U=A*x^2*y+B*x*y^2+C*x*y+D*x+E*y."""

    a_coefficient = (
        first_major_axis / 2 - I * minor_axis_factor * first_minor_axis / 2
    )
    e_coefficient = (
        first_major_axis / 2 + I * minor_axis_factor * first_minor_axis / 2
    )
    b_coefficient = -semimajor_axis_ratio * (
        second_major / 2 - I * second_minor_axis_factor * second_minor / 2
    )
    d_coefficient = -semimajor_axis_ratio * (
        second_major / 2 + I * second_minor_axis_factor * second_minor / 2
    )
    c_coefficient = (
        -eccentricity * first_major_axis
        + semimajor_axis_ratio * second_eccentricity * second_major
    )
    return (
        a_coefficient,
        b_coefficient,
        c_coefficient,
        d_coefficient,
        e_coefficient,
    )


def cubic_forms(
    coefficients: tuple[sym.Matrix, sym.Matrix, sym.Matrix, sym.Matrix, sym.Matrix],
) -> list[sym.Expr]:
    """Homogenized coordinate differences used in P=sum(U_i^2)."""

    a_coefficient, b_coefficient, c_coefficient, d_coefficient, e_coefficient = (
        coefficients
    )
    return [
        sym.expand(
            a_coefficient[index] * x**2 * y
            + b_coefficient[index] * x * y**2
            + c_coefficient[index] * x * y * z
            + d_coefficient[index] * x * z**2
            + e_coefficient[index] * y * z**2
        )
        for index in range(3)
    ]


coefficients = poincare_coefficients(second_major_axis, second_minor_axis)
a_coefficient, b_coefficient, _, d_coefficient, e_coefficient = coefficients
coordinate_differences = cubic_forms(coefficients)
p_polynomial = sym.expand(sum(form**2 for form in coordinate_differences))

tau = sym.Rational(1, 3)
second_tau = sym.Rational(1, 5)
lattice_a = sym.Rational(-2)
lattice_c = sym.Rational(3)

first_factor = (1 + tau**2) * (y - second_tau * z) * (z - second_tau * y)
second_factor = (1 + second_tau**2) * (x - tau * z) * (z - tau * x)
first_reduced = [a_coefficient[index] * x**2 - e_coefficient[index] * z**2 for index in range(3)]
second_reduced = [b_coefficient[index] * y**2 - d_coefficient[index] * z**2 for index in range(3)]
r_polynomial = sym.expand(
    lattice_c
    * first_factor
    * sum(first_reduced[index] * coordinate_differences[index] for index in range(3))
    - lattice_a
    * second_factor
    * sum(second_reduced[index] * coordinate_differences[index] for index in range(3))
)

# This is the exact cleared table copied into `Section103/ReducedCurve.lean`.
# Keeping the independent derivation here makes transcription errors observable without placing
# SymPy in Lean's trusted proof path.
expected_cleared_r_coefficients = {
    (4, 3, 0): -90285 - 99840 * I,
    (4, 2, 1): 136890,
    (4, 1, 2): 112515 + 62400 * I,
    (3, 4, 0): -106500 - 96000 * I,
    (3, 3, 1): 1051430 + 914464 * I,
    (3, 2, 2): -1041300 - 468000 * I,
    (3, 1, 3): 38470 + 186464 * I,
    (3, 0, 4): -88500 - 60000 * I,
    (2, 4, 1): 150000,
    (2, 3, 2): -1388400 - 112320 * I,
    (2, 1, 4): 1388400 - 112320 * I,
    (2, 0, 5): -150000,
    (1, 4, 2): 88500 - 60000 * I,
    (1, 3, 3): -38470 + 186464 * I,
    (1, 2, 4): 1041300 - 468000 * I,
    (1, 1, 5): -1051430 + 914464 * I,
    (1, 0, 6): 106500 - 96000 * I,
    (0, 3, 4): -112515 + 62400 * I,
    (0, 2, 5): -136890,
    (0, 1, 6): 90285 - 99840 * I,
}
assert (
    dict(sym.Poly(438750 * r_polynomial, x, y, z).terms())
    == expected_cleared_r_coefficients
)

assert sym.Poly(p_polynomial, x, y, z).total_degree() == 6
assert sym.Poly(r_polynomial, x, y, z).total_degree() == 7
assert sym.gcd(
    sym.Poly(p_polynomial, x, y, z), sym.Poly(r_polynomial, x, y, z)
).total_degree() == 0


def vanishing_order(polynomial: sym.Expr, variable: sym.Symbol) -> int:
    """Return the least exponent with nonzero coefficient."""

    return min(monomial[0] for monomial, _ in sym.Poly(polynomial, variable).terms())


# The resultant orders isolate the common point (1:0:0), respectively
# (0:1:0), in the two affine charts.  Stable leading coefficients rule out a
# spurious contribution from infinity inside either chart.
x_chart_resultant = sym.resultant(
    p_polynomial.subs(x, 1), r_polynomial.subs(x, 1), y
)
y_chart_resultant = sym.resultant(
    p_polynomial.subs(y, 1), r_polynomial.subs(y, 1), x
)
assert vanishing_order(x_chart_resultant, z) == 8
assert vanishing_order(y_chart_resultant, z) == 8


# At the affine origin P has order two and R order one.  The displayed
# nonzero restriction proves that the tangent line of R is not a component of
# the tangent cone of P, so the local intersection contribution is two.
affine_p = sym.Poly(p_polynomial.subs(z, 1), x, y)
affine_r = sym.Poly(r_polynomial.subs(z, 1), x, y)
p_tangent_cone = sym.expand(
    sum(
        coefficient * x ** monomial[0] * y ** monomial[1]
        for monomial, coefficient in affine_p.terms()
        if sum(monomial) == 2
    )
)
r_tangent_line = sym.expand(
    sum(
        coefficient * x ** monomial[0] * y ** monomial[1]
        for monomial, coefficient in affine_r.terms()
        if sum(monomial) == 1
    )
)
r_x = sym.Poly(r_tangent_line, x, y).coeff_monomial(x)
r_y = sym.Poly(r_tangent_line, x, y).coeff_monomial(y)
assert r_y != 0
assert sym.simplify(p_tangent_cone.subs(y, -r_x * x / r_y) / x**2) != 0


# Infinitesimal rotations of the second ellipse about the three coordinate
# axes.  The rank-four certificate below says that no nonzero relative
# rotation changes P merely by a scalar multiple.  This replaces the informal
# final four-zero-radius-spheres paragraph with an exact tangent-space check.
rotation_generators = [
    sym.Matrix([[0, 0, 0], [0, 0, -1], [0, 1, 0]]),
    sym.Matrix([[0, 0, 1], [0, 0, 0], [-1, 0, 0]]),
    sym.Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 0]]),
]
directional_derivatives: list[sym.Expr] = []
for generator in rotation_generators:
    major_derivative = generator * second_major_axis
    minor_derivative = generator * second_minor_axis
    zero = sym.zeros(3, 1)
    derivative_coefficients = (
        zero,
        -semimajor_axis_ratio
        * (major_derivative / 2 - I * second_minor_axis_factor * minor_derivative / 2),
        semimajor_axis_ratio * second_eccentricity * major_derivative,
        -semimajor_axis_ratio
        * (major_derivative / 2 + I * second_minor_axis_factor * minor_derivative / 2),
        zero,
    )
    derivative_forms = cubic_forms(derivative_coefficients)
    directional_derivatives.append(
        sym.expand(
            2
            * sum(
                coordinate_differences[index] * derivative_forms[index]
                for index in range(3)
            )
        )
    )

certificate_monomials = [(0, 2, 4), (1, 1, 4), (1, 2, 3), (2, 1, 3)]
certificate_columns = directional_derivatives + [-p_polynomial]
certificate_matrix = sym.Matrix(
    [
        [
            sym.Poly(polynomial, x, y, z).coeff_monomial(monomial)
            for polynomial in certificate_columns
        ]
        for monomial in certificate_monomials
    ]
)
certificate_determinant = sym.factor(certificate_matrix.det())
assert certificate_determinant == (
    sym.Rational(90576, 6865625) - sym.Rational(340992, 6865625) * I
)
assert certificate_determinant != 0


# Ruppert's characteristic-zero criterion turns absolute irreducibility of the
# affine polynomial f=P(x,y,1), of bidegree (4,4), into full column rank of a
# 64-by-35 matrix.  Its columns are the coefficients of
#
#   f*g_y + h*f_x - g*f_y - f*h_x,
#
# where deg(g) <= (3,4) and deg(h) <= (4,2).  Full rank closes the precise
# logical gap in Poincare's inference from a common component to equality of
# the degree-six curves.
ruppert_f = sym.Poly(sym.expand(p_polynomial.subs(z, 1)), x, y, extension=I)
ruppert_m = ruppert_f.degree(x)
ruppert_n = ruppert_f.degree(y)
assert (ruppert_m, ruppert_n) == (4, 4)

ruppert_unknowns = [
    ("g", s, t)
    for s in range(ruppert_m)
    for t in range(ruppert_n + 1)
] + [
    ("h", s, t)
    for s in range(ruppert_m + 1)
    for t in range(ruppert_n - 1)
]
ruppert_rows = [
    (x_degree, y_degree)
    for x_degree in range(2 * ruppert_m)
    for y_degree in range(2 * ruppert_n)
]
ruppert_row_index = {monomial: index for index, monomial in enumerate(ruppert_rows)}
ruppert_matrix = sym.zeros(len(ruppert_rows), len(ruppert_unknowns))
ruppert_coefficients = {
    monomial: coefficient for monomial, coefficient in ruppert_f.terms()
}

for column, (kind, s_degree, t_degree) in enumerate(ruppert_unknowns):
    for (x_degree, y_degree), coefficient in ruppert_coefficients.items():
        if kind == "g" and y_degree + t_degree >= 1:
            row = ruppert_row_index[
                (x_degree + s_degree, y_degree + t_degree - 1)
            ]
            ruppert_matrix[row, column] += (t_degree - y_degree) * coefficient
        if kind == "h" and x_degree + s_degree >= 1:
            row = ruppert_row_index[
                (x_degree + s_degree - 1, y_degree + t_degree)
            ]
            ruppert_matrix[row, column] += (x_degree - s_degree) * coefficient

# DomainMatrix performs fraction-free exact linear algebra in Q(i); the
# ordinary symbolic Matrix rank routine is dramatically slower here.
ruppert_domain_matrix = ruppert_matrix.to_DM(extension=True)
_, ruppert_pivot_columns = ruppert_domain_matrix.rref()
assert ruppert_pivot_columns == tuple(range(35))
_, ruppert_pivot_rows = ruppert_domain_matrix.transpose().rref()
assert ruppert_pivot_rows == (
    1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21,
    24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43,
)
ruppert_minor = ruppert_domain_matrix.extract(list(ruppert_pivot_rows), list(range(35)))
assert ruppert_minor.det() != ruppert_domain_matrix.domain.zero


# The Lean irreducibility proof also uses a much smaller squarefreeness certificate.
# Specialize the cleared affine polynomial at x=1, reduce modulo 17, and map i to 4
# (so 4^2=-1). The resulting quartic has the displayed explicit Bézout identity
# with its derivative.
def gaussian_rational_mod17(value: sym.Expr) -> int:
    real, imaginary = sym.expand(value).as_real_imag()

    def rational_mod17(coefficient: sym.Expr) -> int:
        coefficient = sym.Rational(coefficient)
        return (
            int(coefficient.p) % 17
            * pow(int(coefficient.q), -1, 17)
            % 17
        )

    return (rational_mod17(real) + 4 * rational_mod17(imaginary)) % 17


cleared_specialization = sym.Poly(
    sym.expand(50700 * p_polynomial.subs({z: 1, x: 1})), y, extension=I
)
specialized_coefficients = tuple(
    gaussian_rational_mod17(cleared_specialization.coeff_monomial(y**degree))
    for degree in range(5)
)
assert specialized_coefficients == (3, 13, 7, 16, 3)
specialized_polynomial = sym.Poly(
    sum(coefficient * y**degree for degree, coefficient in enumerate(specialized_coefficients)),
    y,
    modulus=17,
)
bezout_left = sym.Poly(y**2 + 7 * y, y, modulus=17)
bezout_right = sym.Poly(4 + 15 * y + 5 * y**2 + 4 * y**3, y, modulus=17)
assert bezout_left * specialized_polynomial + bezout_right * specialized_polynomial.diff() == 1
assert int(sym.resultant(specialized_polynomial, specialized_polynomial.diff())) % 17 == 2

print("gcd(P,R) = 1")
print("local contributions: origin=2, x-infinity=8, y-infinity=8")
print(f"rotation certificate determinant = {certificate_determinant}")
print("Ruppert matrix: shape=(64,35), rank=35")
print("squarefreeness specialization: resultant=2 mod 17")
