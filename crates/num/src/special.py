# Writes special.txt: complex functions on a grid of special values, as C99 Annex G pins them
# down. Values come from, in order:
#   1. CPython's hand-checked cmath_testcases.txt, if given (it ships in Python's test suite,
#      as Lib/test/mathdata/cmath_testcases.txt), which also says where a sign is unspecified;
#   2. Python's cmath, which follows Annex G but raises where it would set a floating-point flag;
#   3. the C library, which fills in the rest. Apple's libm drops some zero signs, so it's
#      asked about the conjugate of inputs with a negative imaginary part, as every one of these
#      functions has f(conj z) = conj f(z), and the inputs it decides go to stderr to be
#      checked by hand.
#     python3 -I special.py [cmath_testcases.txt] > special.txt
# Each line is a function, the input's and the result's parts as the hex bits of doubles, and
# which result signs are unspecified: r, i, ri or -.
import cmath
import ctypes
import ctypes.util
import math
import struct
import sys


class Complex(ctypes.Structure):
    # Laid out and passed like `double complex` on the usual 64-bit ABIs.
    _fields_ = [("re", ctypes.c_double), ("im", ctypes.c_double)]


FUNCTIONS = ["exp", "log", "sqrt", "sin", "cos", "tan", "asin", "acos", "atan"]
PARTS = [0.0, -0.0, 0.5, 1.0, -1.0, 2.0, 709.9, -1000.0, math.inf, -math.inf, math.nan]


def bits(f):
    return format(struct.unpack("<Q", struct.pack("<d", f))[0], "016x")


def checked_cases(path):
    cases = {}
    for line in open(path):
        if line.startswith("--") or "->" not in line:
            continue
        left, right = line.split("->")
        _, name, re, im = left.split()
        out = right.split()
        signs = ("r" if "ignore-real-sign" in out else "") + ("i" if "ignore-imag-sign" in out else "")
        cases[name, bits(float(re)), bits(float(im))] = (float(out[0]), float(out[1]), signs or "-")
    return cases


checked = checked_cases(sys.argv[1]) if len(sys.argv) > 1 else {}
libm = ctypes.CDLL(ctypes.util.find_library("m"))
for name in FUNCTIONS:
    f = getattr(libm, "c" + name)
    f.restype, f.argtypes = Complex, [Complex]
    for re in PARTS:
        for im in PARTS:
            key = (name, bits(re), bits(im))
            if key in checked:
                w_re, w_im, signs = checked[key]
            else:
                signs = "-"
                try:
                    w = getattr(cmath, name)(complex(re, im))
                except (ValueError, OverflowError):
                    flip = math.copysign(1.0, im) < 0
                    c = f(Complex(re, -im if flip else im))
                    w = complex(c.re, -c.im if flip else c.im)
                    print(f"{name}({re!r}, {im!r}) from libm: {w!r}", file=sys.stderr)
                w_re, w_im = w.real, w.imag
            print(name, bits(re), bits(im), bits(w_re), bits(w_im), signs)
