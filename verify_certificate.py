#!/usr/bin/env python3
"""Certify the 47 numerical conditions of the aligned-cache APSP construction.

Python standard library only. No floating-point number participates in a
verification. This independently implemented checker certifies inequalities,
not the inherited embedding, data structure, reduction, or word-RAM program.

Usage: python3 verify_certificate.py [--json certificate.json]
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path


def require(condition, message):
    # Explicit failures remain active under python -O.
    if not condition:
        raise ArithmeticError(message)


@dataclass(frozen=True)
class Bounds:
    lo: Q
    hi: Q

    def __post_init__(self):
        require(self.lo <= self.hi, "Reversed interval")

    @staticmethod
    def point(x):
        return x if isinstance(x, Bounds) else Bounds(Q(x), Q(x))

    def __add__(self, other):
        b = self.point(other)
        return Bounds(self.lo + b.lo, self.hi + b.hi)

    __radd__ = __add__

    def __neg__(self):
        return Bounds(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.point(other)

    def __rsub__(self, other):
        return self.point(other) + -self

    def __mul__(self, other):
        b = self.point(other)
        xs = [a * c for a in (self.lo, self.hi) for c in (b.lo, b.hi)]
        return Bounds(min(xs), max(xs))

    __rmul__ = __mul__

    def __truediv__(self, other):
        b = self.point(other)
        require(b.lo > 0, "Division needs a strictly positive denominator")
        return self * Bounds(1 / b.hi, 1 / b.lo)


@lru_cache(None)
def unit_log(x: Q) -> Bounds:
    """Exact rational enclosure of ln(x), 1 <= x <= 2, with 40 terms.

    ln(x) = 2 sum_{j>=0} z^(2j+1)/(2j+1), z=(x-1)/(x+1).
    After j=0,...,39, the tail is between zero and
    2 z^81 / (81 (1-z^2)). Every quantity below is a Fraction.
    """
    require(1 <= x <= 2, "Log range reduction failed")
    z = (x - 1) / (x + 1)
    z2 = z * z
    power, partial = z, Q(0)
    for j in range(40):
        partial += power / (2 * j + 1)
        power *= z2
    lower = 2 * partial
    upper = lower + 2 * power / (81 * (1 - z2))
    return Bounds(lower, upper)


@lru_cache(None)
def log(x: Q) -> Bounds:
    x = Q(x)
    require(x > 0, "Log argument must be positive")
    power_of_two = 0
    while x < 1:
        x *= 2
        power_of_two -= 1
    while x >= 2:
        x /= 2
        power_of_two += 1
    return unit_log(x) + power_of_two * unit_log(Q(2))


def entropy(x: Q) -> Bounds:
    require(0 < x < 1, "Entropy argument must be in (0,1)")
    return -x * log(x) - (1 - x) * log(1 - x)


def decimal_bound(x: Q, digits=28, upward=False) -> str:
    scale = 10 ** digits
    value = -((-x.numerator * scale) // x.denominator) if upward else (x.numerator * scale) // x.denominator
    sign = "-" if value < 0 else ""
    value = abs(value)
    return f"{sign}{value // scale}.{value % scale:0{digits}d}"


def display_interval(x):
    x = Bounds.point(x)
    return {"lower": decimal_bound(x.lo), "upper": decimal_bound(x.hi, upward=True)}


def verify():
    p = json.loads(Path(__file__).with_name("parameters.json").read_text())
    c, theta, b, delta = (Q(p[k]) for k in ("c", "theta", "b", "delta"))
    R, S = int(p["R"]), int(p["S"])
    require(R > S > 0, "Expected R > S > 0")
    require(0 < delta < 1, "Invalid target saving")
    eta = b / R
    u, v = S * eta, (R - S) * eta
    e = b + u
    require(Q(p["exponent"]) == 3 - delta, "Exponent and saving disagree")
    require(u + v == b and R * eta == b and S * eta == u, "Stage identity failed")

    ln2, ln4 = log(Q(2)), log(Q(4))
    ck = c * entropy(1 / c) / ln4
    T = c - 1 + ck
    G = (c * entropy(1 / c) - c * entropy((1 - theta) / c) - theta * ln4) / ln2
    q1 = entropy(theta) / ln2
    q2 = q1 + 2 * theta
    E, Ebox = T + q1, T - G

    checks = []
    def check(label, value, threshold=0, runtime=False):
        value, threshold = Bounds.point(value), Q(threshold)
        require(value.lo > threshold, f"FAIL: {label}: {display_interval(value)} <= {threshold}")
        row = {"condition": label, "value": display_interval(value),
               "threshold": str(threshold),
               "strict_gap_lower": decimal_bound(value.lo - threshold),
               "runtime": runtime, "passed": True}
        checks.append(row)
        print(f"PASS {label}: [{row['value']['lower']}, {row['value']['upper']}] > {threshold}")

    for label, value, target in [
        ("ordinary tail c > 5", c - 5, 0),
        ("theta > 0", theta, 0),
        ("unweighted binomial tail increasing", Q(1, 2) - theta, 0),
        ("stored binomial tail increasing", Q(4, 5) - theta, 0),
        ("ordinary private tail geometric", 1 - 4 / (c - 1), 0),
        ("box private tail geometric", 1 - 4 * (1 - theta) / (c - 1 + theta), 0),
        ("G > 0", G, 0), ("G < 1", 1 - G, 0),
        ("q1 > 0", q1, 0), ("q2 > 0", q2, 0),
        ("cache slope positive", E + Q(1, 2), 0),
        ("ordinary encoder slope positive", Ebox + Q(1, 2), 0),
        ("geometry slope positive", T - Q(1, 2), 0),
        ("frozen factors positive", Q(S), 0),
        ("at least two cyclic factors", Q(R - S), 1),
        ("cyclic exponent positive", v, 0),
        ("candidate exponent positive", eta, 0),
        ("middle blocks fit", 1 - b, 0),
    ]:
        check(label, value, target)
    check("incidence bookkeeping", b - eta, delta, True)

    for endpoint, x in [("initial", Q(0)), ("freeze", u)]:
        ep = b + x
        terms = [
            ("boxes", b - x + ep * G - eta),
            ("residual queries", b - ep * q1 - eta),
            ("stored queries", b - ep * q2 - eta),
            ("polynomial cache", 1 + b - x / 2 - ep * E - eta),
            ("ordinary box encodings", 1 + b - x / 2 - ep * Ebox - eta),
            ("matrix formation", 1 - 3 * x / 2 - eta),
        ]
        for label, value in terms:
            check(f"phase I {endpoint}: {label}", value, delta, True)
        check(f"phase I {endpoint}: tile geometry", 1 + x / 2 - ep * T)

    for endpoint, z in [("start", Q(0)), ("final", v)]:
        terms = [
            ("boxes", b - u - z + e * G - eta),
            ("residual queries", b - z - e * q1 - eta),
            ("stored queries", b - e * q2 - eta),
            ("polynomial cache", 1 + b - u / 2 - z - e * E - eta),
            ("ordinary box encodings", 1 + b - u / 2 - z - e * Ebox - eta),
            ("matrix formation", 1 - 3 * u / 2 - z - eta),
        ]
        for label, value in terms:
            check(f"phase II {endpoint}: {label}", value, delta, True)
        check(f"phase II {endpoint}: tile geometry", 1 + u / 2 - e * T)

    require(len(checks) == 47, "Unexpected check count")
    runtime_checks = [x for x in checks if x["runtime"]]
    minimum = min(runtime_checks, key=lambda x: Q(x["strict_gap_lower"]))
    result = {"parameters": p,
        "derived": {k: display_interval(value) for k, value in
            [("eta", eta), ("u", u), ("v", v), ("e", e), ("C_K", ck),
             ("T", T), ("G", G), ("q1", q1), ("q2", q2), ("E", E), ("Ebox", Ebox)]},
        "checks_passed": len(checks), "stage_identities_passed": True,
        "smallest_runtime_gap": minimum["strict_gap_lower"],
        "binding_condition": minimum["condition"], "checks": checks}
    print(f"\nPASS: {len(checks)} strict rational inequalities and all exact stage identities.")
    print("Certified exponent:", p["exponent"])
    print("Smallest certified runtime gap:", result["smallest_runtime_gap"])
    print("This certifies numerical feasibility, not the full word-RAM theorem.")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="Write a machine-readable certificate")
    args = parser.parse_args()
    result = verify()
    if args.json:
        args.json.write_text(json.dumps(result, indent=2) + "\n")
