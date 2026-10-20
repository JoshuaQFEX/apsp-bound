#!/usr/bin/env python3
"""Explore the balanced stationary point using 80-digit Decimal arithmetic.

Standard library only. This numerical search is not a certificate or a global
optimality proof. verify_certificate.py independently checks fixed rationals.
"""
from decimal import Decimal as D, localcontext


def equations(c, theta):
    ln2, ln4 = D(2).ln(), D(4).ln()
    entropy = -theta * theta.ln() - (1 - theta) * (1 - theta).ln()
    A = c * c.ln() - (c - 1) * (c - 1).ln()
    T = c - 1 + A / ln4
    G = ((1 - theta) * (1 - theta).ln()
         + (c - 1 + theta) * (c - 1 + theta).ln()
         - (c - 1) * (c - 1).ln() - 2 * theta * ln2) / ln2
    q1 = entropy / ln2
    Gc = ((c - 1 + theta) / (c - 1)).ln() / ln2
    Gt = ((c - 1 + theta) / (4 * (1 - theta))).ln() / ln2
    qt = ((1 - theta) / theta).ln() / ln2
    Tc = 1 + (c / (c - 1)).ln() / ln4
    Ft = Gt + qt + 1
    denominator = T + D('.25') - theta / 2
    balance = G + q1 + theta - D('.5')
    # d/dc of G/denominator along balance=0, after clearing denominators.
    stationary = Gc * (qt + 1) * denominator - G * (Tc * Ft + Gc / 2)
    return balance, stationary, (T, G, q1, denominator)


def search():
    c, theta, h = D('10.6655'), D('.0652978'), D('1e-25')
    for _ in range(12):
        f, g, _ = equations(c, theta)
        cp, cm = equations(c + h, theta), equations(c - h, theta)
        tp, tm = equations(c, theta + h), equations(c, theta - h)
        a, cc = (cp[0] - cm[0]) / (2 * h), (cp[1] - cm[1]) / (2 * h)
        bb, d = (tp[0] - tm[0]) / (2 * h), (tp[1] - tm[1]) / (2 * h)
        det = a * d - bb * cc
        c, theta = c - (d * f - bb * g) / det, theta - (-cc * f + a * g) / det
    f, g, (T, G, q1, denominator) = equations(c, theta)
    e = 1 / denominator
    u = e * (q1 + G)
    b = e - u
    for key, value in [("c", c), ("theta", theta), ("b", b), ("u", u),
                       ("e", e), ("delta_limit", e * G), ("exponent_limit", 3 - e * G),
                       ("balance_residual", f), ("stationarity_residual", g)]:
        print(key, value)
    print("Numerical stationary point only; not a proof of a global optimum.")
    print("Finite stage counts and rounding are checked separately by verify_certificate.py.")


if __name__ == "__main__":
    with localcontext() as context:
        context.prec = 80
        search()
