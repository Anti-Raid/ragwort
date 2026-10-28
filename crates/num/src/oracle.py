# Answers the bigint tests: one operation per line, numbers in hex.
import cmath
import math
import struct
import sys
from fractions import Fraction

CHARS = "0123456789abcdefghijklmnopqrstuvwxyz"


def h(v):
    return format(v, "x")


def radix(v, r):
    out = []
    while v:
        v, d = divmod(v, r)
        out.append(CHARS[d])
    return "".join(reversed(out)) or "0"


def quot(x, y):
    q = abs(x) // abs(y)
    return q if (x < 0) == (y < 0) else -q


def signed_radix(v, r):
    return "-" + radix(-v, r) if v < 0 else radix(v, r)


def f64(v):
    try:
        f = float(v)
    except OverflowError:
        f = float("-inf") if v < 0 else float("inf")
    return h(struct.unpack("<Q", struct.pack("<d", f))[0])


def fr(v):
    v = Fraction(v)
    return h(v.numerator) if v.denominator == 1 else f"{h(v.numerator)}/{h(v.denominator)}"


def number(a):
    if "/" in a:
        num, den = a.split("/")
        return Fraction(int(num, 16), int(den, 16))
    return int(a, 16)


def bits_to_f64(b):
    return struct.unpack("<d", struct.pack("<Q", b))[0]


OPS = {
    "add": lambda x, y: h(x + y),
    "sub": lambda x, y: h(x - y),
    "cmp": lambda x, y: str((x > y) - (x < y)),
    "mul": lambda x, y: h(x * y),
    "divrem": lambda x, y: f"{h(x // y)} {h(x % y)}",
    "shl": lambda x, s: h(x << s),
    "shr": lambda x, s: h(x >> s),
    "lost": lambda x, s: str(int(x & ((1 << s) - 1) != 0)),
    "and": lambda x, y: h(x & y),
    "or": lambda x, y: h(x | y),
    "xor": lambda x, y: h(x ^ y),
    "f64": f64,
    "radix": signed_radix,
    "quot": lambda x, y: h(quot(x, y)),
    "rem": lambda x, y: h(x - y * quot(x, y)),
    "mod": lambda x, y: h(x % y),
    "fquot": lambda x, y: h(x // y),
    "gcd": lambda x, y: h(math.gcd(x, y)),
    "isqrt": lambda x: h(math.isqrt(x)),
    "lcm": lambda x, y: h(math.lcm(x, y)),
    "even": lambda x: str(int(x % 2 == 0)),
    "ilen": lambda x: h(x.bit_length() if x >= 0 else (~x).bit_length()),
    "neg": lambda x: h(-x),
    "abs": lambda x: h(abs(x)),
    "not": lambda x: h(~x),
    "i64": lambda x: h(x) if -(1 << 63) <= x < 1 << 63 else "none",
    "ash": lambda x, s: h(x << s if s >= 0 else x >> -s),
    "expt": lambda x, e: h(x**e),
    "fromf64": lambda b: h(int(bits_to_f64(b))),
    "radd": lambda x, y: fr(x + y),
    "rsub": lambda x, y: fr(x - y),
    "rmul": lambda x, y: fr(x * y),
    "rdiv": lambda x, y: fr(Fraction(x) / y),
    "rcmp": lambda x, y: str((x > y) - (x < y)),
    "floor": lambda x: h(math.floor(x)),
    "ceiling": lambda x: h(math.ceil(x)),
    "truncate": lambda x: h(math.trunc(x)),
    "round": lambda x: h(round(x)),
    "rexpt": lambda x, e: fr(Fraction(x) ** e),
    "rfromf64": lambda b: fr(Fraction(bits_to_f64(b))),
    "parts": lambda n, d: fr(Fraction(n, d)),
}

# The tower, with Racket's rules: ints and Fractions are exact, floats are flonums, and
# complex numbers are ("c", re, im) with parts of the shapes Racket allows.

INF, NAN = math.inf, math.nan


class Fail(Exception):
    pass


def tower(a):
    if a.startswith("cx"):
        re, im = a[2:].split("|")
        return ("c", tower(re), tower(im))
    if a.startswith("fl"):
        return bits_to_f64(int(a[2:], 16))
    return number(a)


def shown(v):
    if isinstance(v, tuple):
        return f"cx{shown(v[1])}|{shown(v[2])}"
    if isinstance(v, float):
        return "fl" + h(struct.unpack("<Q", struct.pack("<d", v))[0])
    return fr(v)


def exact(v):
    if isinstance(v, tuple):
        return exact(v[1]) and exact(v[2])
    return not isinstance(v, float)


def zero(v):
    return not isinstance(v, (float, tuple)) and v == 0


def flo(v):
    if isinstance(v, float):
        return v
    try:
        return float(v)
    except OverflowError:
        return INF if v > 0 else -INF


def fdiv(a, b):
    try:
        return a / b
    except ZeroDivisionError:
        if a != a or a == 0:
            return NAN
        return math.copysign(INF, a) * math.copysign(1.0, b)


def add(x, y):
    return x + y if exact(x) and exact(y) else flo(x) + flo(y)


def sub(x, y):
    return x - y if exact(x) and exact(y) else flo(x) - flo(y)


def mul(x, y):
    if exact(x) and exact(y):
        return x * y
    if zero(x) or zero(y):
        return 0
    return flo(x) * flo(y)


def div(x, y):
    if zero(y):
        raise Fail("div0")
    if exact(x) and exact(y):
        return Fraction(x) / y
    if zero(x):
        return 0
    return fdiv(flo(x), flo(y))


def isnan(v):
    return isinstance(v, float) and v != v


def cmp(x, y):
    if isnan(x) or isnan(y):
        return None
    return (x > y) - (x < y)


def extreme(x, y, want):
    c = cmp(y, x)
    if c is None:
        return NAN
    pick = y if c == want else x
    return pick if exact(x) and exact(y) else flo(pick)


def fround(f, op):
    if not math.isfinite(f):
        return f
    r = float(op(f))
    return math.copysign(0.0, f) if r == 0 else r


ROUNDS = {"floor": math.floor, "ceiling": math.ceil, "truncate": math.trunc, "round": round}


def xround(mode, x):
    if exact(x):
        return ROUNDS[mode](Fraction(x))
    return fround(x, ROUNDS[mode])


def numer(x):
    if exact(x):
        return Fraction(x).numerator
    if not math.isfinite(x):
        raise Fail("noexact")
    return x if x == int(x) else flo(Fraction(x).numerator)


def denom(x):
    if exact(x):
        return Fraction(x).denominator
    if not math.isfinite(x):
        raise Fail("noexact")
    return 1.0 if x == int(x) else flo(Fraction(x).denominator)


def integer(v):
    if exact(v):
        if Fraction(v).denominator != 1:
            raise Fail("notint")
        return int(v)
    if not math.isfinite(v) or v != int(v):
        raise Fail("notint")
    return int(v)


def negative(v):
    return math.copysign(1.0, flo(v)) < 0


def intop(x, y, op, negzero):
    a, b = integer(x), integer(y)
    if b == 0:
        raise Fail("div0")
    n = op(a, b)
    if exact(x) and exact(y):
        return n
    f = float(n)
    return -0.0 if f == 0 and negzero(x, y) else f


INTOPS = {
    "xquotient": (quot, lambda x, y: negative(x) != negative(y)),
    "xremainder": (lambda a, b: a - b * quot(a, b), lambda x, y: negative(x)),
    "xmodulo": (lambda a, b: a % b, lambda x, y: negative(y)),
}


def inexact(z):
    if isinstance(z, tuple):
        return ("c", flo(z[1]), flo(z[2]))
    return flo(z)


def to_exact(z):
    if isinstance(z, tuple):
        return rect(to_exact(z[1]), to_exact(z[2]))
    if exact(z):
        return z
    if not math.isfinite(z):
        raise Fail("noexact")
    return Fraction(z)


def parts(z):
    return (z[1], z[2]) if isinstance(z, tuple) else (z, 0)


def rect(re, im):
    if zero(im):
        return re
    if exact(re) == exact(im) or zero(re):
        return ("c", re, im)
    return ("c", flo(re), flo(im))


def neg(x):
    return -x


def cadd(x, y):
    if not isinstance(x, tuple) and not isinstance(y, tuple):
        return add(x, y)
    if not isinstance(x, tuple):
        return rect(add(x, y[1]), y[2])
    if not isinstance(y, tuple):
        return rect(add(x[1], y), x[2])
    return rect(add(x[1], y[1]), add(x[2], y[2]))


def csub(x, y):
    if not isinstance(x, tuple) and not isinstance(y, tuple):
        return sub(x, y)
    if not isinstance(x, tuple):
        return rect(sub(x, y[1]), neg(y[2]))
    if not isinstance(y, tuple):
        return rect(sub(x[1], y), x[2])
    return rect(sub(x[1], y[1]), sub(x[2], y[2]))


def cmul(x, y):
    if not isinstance(x, tuple) and not isinstance(y, tuple):
        return mul(x, y)
    if not isinstance(x, tuple):
        return rect(mul(x, y[1]), mul(x, y[2]))
    if not isinstance(y, tuple):
        return rect(mul(y, x[1]), mul(y, x[2]))
    (a, b), (c, d) = parts(x), parts(y)
    return rect(sub(mul(a, c), mul(b, d)), add(mul(a, d), mul(b, c)))


def cdiv(x, y):
    if not isinstance(y, tuple):
        if zero(y):
            raise Fail("div0")
        if not isinstance(x, tuple):
            return div(x, y)
        return rect(div(x[1], y), div(x[2], y))
    if zero(x):
        return x
    if exact(x) and exact(y):
        (a, b), (c, d) = parts(x), parts(y)
        den = c * c + d * d
        return rect(Fraction(a * c + b * d) / den, Fraction(b * c - a * d) / den)
    return from_complex(smith(to_complex(x), to_complex(y)))


def smith(a, b):
    """Smith's division in plain float steps. CPython's own complex division gives other
    bits on machines where its C compiler fuses multiplies and adds."""
    if abs(b.real) >= abs(b.imag):
        ratio = fdiv(b.imag, b.real)
        d = b.real + b.imag * ratio
        return complex(fdiv(a.real + a.imag * ratio, d), fdiv(a.imag - a.real * ratio, d))
    if abs(b.imag) >= abs(b.real):
        ratio = fdiv(b.real, b.imag)
        d = b.real * ratio + b.imag
        return complex(fdiv(a.real * ratio + a.imag, d), fdiv(a.imag * ratio - a.real, d))
    return complex(NAN, NAN)


def to_complex(z):
    a, b = parts(z)
    return complex(flo(a), flo(b))


def from_complex(c):
    return ("c", c.real, c.imag)


def equal(x, y):
    (a, b), (c, d) = parts(x), parts(y)
    return str(int(cmp(a, c) == 0 and cmp(b, d) == 0))


def exact_root(r):
    r = Fraction(r)
    n, d = math.isqrt(r.numerator), math.isqrt(r.denominator)
    return Fraction(n, d) if n * n == r.numerator and d * d == r.denominator else None


def split(r):
    r = Fraction(r)
    n = r.numerator
    k = (n if n >= 0 else ~n).bit_length() - r.denominator.bit_length()
    return float(r / Fraction(2) ** k), k


def normal(f):
    return math.isfinite(f) and abs(f) >= sys.float_info.min


def sqrt_real(x):
    if not exact(x):
        return math.sqrt(x) if not x < 0 else NAN
    s = exact_root(x)
    if s is not None:
        return s
    f = flo(x)
    if normal(f):
        return math.sqrt(f)
    m, k = split(x)
    if k % 2:
        m, k = m * 2, k - 1
    return math.ldexp(math.sqrt(m), k // 2)


def log_real(x):
    if not exact(x):
        if x == 0:
            return -INF
        return math.log(x) if math.isfinite(x) else x
    if x == 0:
        raise Fail("div0")
    if x == 1:
        return 0
    f = flo(x)
    if normal(f):
        return math.log(f)
    m, k = split(x)
    return math.log(m) + k * math.log(2)


def exact_pair(a, b):
    fa, fb = flo(a), flo(b)
    if (normal(fa) or a == 0) and (normal(fb) or b == 0):
        return fa, fb
    k = max(split(r)[1] for r in (a, b) if r != 0)
    s = Fraction(2) ** -k
    return float(Fraction(a) * s), float(Fraction(b) * s)


def angle(z):
    if not isinstance(z, tuple):
        if exact(z):
            if z == 0:
                raise Fail("div0")
            return 0 if z > 0 else math.pi
        if z != z:
            return z
        return math.pi if math.copysign(1.0, z) < 0 else 0
    a, b = z[1], z[2]
    if exact(a) and exact(b):
        fa, fb = exact_pair(a, b)
    else:
        fa, fb = flo(a), flo(b)
    return math.atan2(fb, fa)


def magnitude(z):
    if not isinstance(z, tuple):
        return abs(z)
    a, b = z[1], z[2]
    if exact(a) and exact(b):
        return sqrt_real(Fraction(a) ** 2 + Fraction(b) ** 2)
    return math.hypot(flo(a), flo(b))


def csqrt(z):
    if not isinstance(z, tuple):
        if (exact(z) and z < 0) or (not exact(z) and z < 0):
            return rect(0, sqrt_real(-z))
        return sqrt_real(z)
    a, b = z[1], z[2]
    if exact(a) and exact(b):
        m = exact_root(Fraction(a) ** 2 + Fraction(b) ** 2)
        if m is not None:
            p, q = exact_root((m + a) / 2), exact_root((m - a) / 2)
            if p is not None and q is not None:
                return rect(p, -q if b < 0 else q)
    return from_complex(cmath.sqrt(to_complex(z)))


def safe(f, x):
    try:
        return f(x)
    except ValueError:
        return NAN
    except OverflowError:
        return INF


def cexp(z):
    if zero(z):
        return 1
    if not isinstance(z, tuple):
        return safe(math.exp, flo(z))
    return from_complex(cmath.exp(to_complex(z)))


def clog(z):
    if not isinstance(z, tuple) and not (z < 0):
        return log_real(z)
    if not isinstance(z, tuple):
        return rect(log_real(magnitude(z)), angle(z))
    return rect(log_real(magnitude(z)), angle(z)) if exact(z) else from_complex(cmath.log(to_complex(z)))


def trig(real, cm, exact_zero):
    def f(z):
        if exact_zero and zero(z):
            return 0
        if not isinstance(z, tuple):
            return safe(real, flo(z))
        return from_complex(cm(to_complex(z)))
    return f


def inverse(real, cm, exact_zero):
    def f(z):
        if exact_zero and zero(z):
            return 0
        if not isinstance(z, tuple):
            x = flo(z)
            if not abs(x) > 1:
                return real(x)
            return from_complex(cm(complex(x, 0.0)))
        return from_complex(cm(to_complex(z)))
    return f


def catan(z):
    if zero(z):
        return 0
    if not isinstance(z, tuple):
        return math.atan(flo(z))
    if zero(z[1]) and exact(z[2]) and abs(z[2]) == 1:
        raise Fail("div0")
    return from_complex(cmath.atan(to_complex(z)))


def atan2(y, x):
    if zero(y):
        if zero(x):
            raise Fail("div0")
        if cmp(x, 0) == 1:
            return y
    if exact(y) and exact(x):
        fy, fx = exact_pair(y, x)
    else:
        fy, fx = flo(y), flo(x)
    return math.atan2(fy, fx)


def polar(m, a):
    f = flo(a)
    s = a if zero(a) else math.sin(f) if math.isfinite(f) else NAN
    c = math.cos(f) if math.isfinite(f) else NAN
    return rect(mul(m, c), mul(m, s))


def cpow(a, b):
    """C99 pow, which Python's math.pow raises on instead of returning."""
    try:
        return math.pow(a, b)
    except (ValueError, ZeroDivisionError):
        if a == 0 and b < 0:
            odd = b == int(b) and int(b) % 2 == 1
            return math.copysign(INF, a) if odd else INF
        return NAN
    except OverflowError:
        odd = math.isfinite(b) and b == int(b) and int(b) % 2 == 1
        return -INF if a < 0 and odd else INF


def is_one(z):
    return not isinstance(z, tuple) and exact(z) and z == 1


def is_flo(v, f):
    return isinstance(v, float) and v == f


def expt(z, w):
    if zero(w) or is_one(z):
        return 1
    if zero(z):
        if not isinstance(w, tuple):
            if is_flo(w, 0.0):
                return 1.0
            if isnan(w):
                return w
            if w < 0:
                raise Fail("div0")
            return z
        c = cmp(w[1], 0)
        if c == 1:
            return z
        if c is None:
            return NAN
        raise Fail("div0")
    if isinstance(w, tuple):
        return cexp(cmul(w, clog(z)))
    if exact(w):
        q = Fraction(w)
        if q.denominator == 1:
            return integer_power(z, int(q))
        if q == Fraction(1, 2):
            return csqrt(z)
    if not isinstance(z, tuple):
        if is_flo(w, 0.0) or is_flo(z, 1.0):
            return 1.0
        fb, fe = flo(z), flo(w)
        if not (cmp(z, 0) == -1) or (not exact(w) and math.isfinite(fe) and fe == int(fe)):
            return cpow(fb, fe)
    return cexp(cmul(w, clog(z)))


def fits_i64(n):
    return -(1 << 63) <= n < 1 << 63


def integer_power(z, n):
    if not isinstance(z, tuple):
        if not exact(z):
            return cpow(z, flo(n))
        if not fits_i64(n):
            if z == -1:
                return 1 if n % 2 == 0 else -1
            raise Fail("toobig")
        return Fraction(z) ** n
    if not fits_i64(n):
        if exact(z):
            raise Fail("toobig")
        return cexp(cmul(n, clog(z)))
    result, base, left = 1, z, abs(n)
    while left:
        if left & 1:
            result = cmul(result, base)
        left >>= 1
        if left:
            base = cmul(base, base)
    return cdiv(1, result) if n < 0 else result


def near(want, ours, loose):
    """Exact parts must match exactly, and flonums to the bit unless `loose`, which allows
    a few ulps of the whole number's magnitude."""
    if isinstance(want, tuple) != isinstance(ours, tuple):
        return False
    if isinstance(want, tuple):
        scale = max(abs(flo(want[1])), abs(flo(want[2])))
        return all(near_part(w, o, loose, scale) for w, o in zip(want[1:], ours[1:]))
    return near_part(want, ours, loose, abs(flo(want)))


def near_part(w, o, loose, scale):
    if exact(w) or exact(o):
        return exact(w) and exact(o) and Fraction(w) == Fraction(o)
    if w != w or o != o:
        return w != w and o != o
    if w == o and math.copysign(1, w) == math.copysign(1, o):
        return True
    if not loose or not math.isfinite(w) or not math.isfinite(o) or not math.isfinite(scale):
        return False
    return abs(w - o) <= 16 * sys.float_info.epsilon * max(scale, sys.float_info.min)


FUNCTIONS = {
    "sqrt": csqrt,
    "exp": cexp,
    "log": clog,
    "sin": trig(math.sin, cmath.sin, True),
    "cos": trig(math.cos, cmath.cos, False),
    "tan": trig(math.tan, cmath.tan, True),
    "asin": inverse(math.asin, cmath.asin, True),
    "acos": inverse(math.acos, cmath.acos, False),
    "atan": catan,
    "magnitude": magnitude,
    "angle": angle,
    "expt": expt,
    "logb": lambda z, b: cdiv(clog(z), clog(b)),
    "atan2": atan2,
    "polar": polar,
}


ERRORS = ("div0", "noexact", "notint", "toobig")


def attempt(f, *args):
    try:
        return f(*args)
    except Fail as e:
        return str(e)


def answer(op, args):
    if op in OPS:
        return OPS[op](*(number(a) for a in args))
    if op == "near":
        # near <function> <loose> <args...> <ours>
        name, loose, inputs, ours = args[0], args[1] == "1", [tower(a) for a in args[2:-1]], args[-1]
        try:
            want = attempt(FUNCTIONS[name], *inputs)
        except (ValueError, OverflowError):
            # cmath raises where C99 gives infinities, so there's nothing to compare with.
            return "ok"
        if isinstance(want, str) or ours in ERRORS:
            return "ok" if want == ours else f"want {want if isinstance(want, str) else shown(want)}"
        return "ok" if near(want, tower(ours), loose) else f"want {shown(want)}"
    v = [tower(a) for a in args]
    if op == "xadd":
        return attempt(lambda: shown(cadd(*v)))
    if op == "xsub":
        return attempt(lambda: shown(csub(*v)))
    if op == "xmul":
        return attempt(lambda: shown(cmul(*v)))
    if op == "xdiv":
        return attempt(lambda: shown(cdiv(*v)))
    if op == "xcmp":
        c = cmp(*v)
        return "nan" if c is None else str(c)
    if op in ("xmax", "xmin"):
        return shown(extreme(v[0], v[1], 1 if op == "xmax" else -1))
    if op == "xeq":
        return equal(*v)
    if op[1:] in ROUNDS:
        return shown(xround(op[1:], v[0]))
    if op == "xnumerator":
        return attempt(lambda: shown(numer(v[0])))
    if op == "xdenominator":
        return attempt(lambda: shown(denom(v[0])))
    if op in INTOPS:
        f, negzero = INTOPS[op]
        return attempt(lambda: shown(intop(v[0], v[1], f, negzero)))
    if op == "xinexact":
        return shown(inexact(v[0]))
    if op == "xexact":
        return attempt(lambda: shown(to_exact(v[0])))
    if op == "xrect":
        return shown(rect(*v))
    raise KeyError(op)


out = []
for line in sys.stdin:
    op, *args = line.split()
    out.append(answer(op, args))
sys.stdout.write("\n".join(out) + "\n")
