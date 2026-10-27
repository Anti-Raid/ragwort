//! Complex arithmetic on pairs of doubles. Square roots, exponentials and the inverse
//! functions follow CPython's `cmath`, which takes them from Kahan's "Branch Cuts for Complex
//! Elementary Functions", so they keep signed zeros on the right side of each branch cut.

use std::f64::consts::{E, FRAC_PI_2, LN_2};

#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct C {
    pub re: f64,
    pub im: f64,
}

const fn c(re: f64, im: f64) -> C {
    C { re, im }
}

const LARGE: f64 = f64::MAX / 4.0;
/// `ln(LARGE)`: `exp` overflows a little past it.
const LOG_LARGE: f64 = 708.3964185322641;
/// `sqrt(LARGE)` and `sqrt(f64::MIN_POSITIVE)`.
const SQRT_LARGE: f64 = 6.703903964971299e153;
const SQRT_MIN: f64 = 1.4916681462400413e-154;

/// `x * 2^k`, with one rounding unless the result is far below the normal range.
pub(crate) fn ldexp(mut x: f64, k: i64) -> f64 {
    let mut k = k.clamp(-2200, 2200);
    let power = |k: i64| f64::from_bits(((k + 1023) as u64) << 52);
    while k > 1023 {
        x *= power(1023);
        k -= 1023;
    }
    while k < -1022 {
        x *= power(-1022);
        k += 1022;
    }
    x * power(k)
}

/// Smith's division, as CPython does it.
pub(crate) fn div(a: C, b: C) -> C {
    let (abs_re, abs_im) = (b.re.abs(), b.im.abs());
    if abs_re >= abs_im {
        let ratio = b.im / b.re;
        let denom = b.re + b.im * ratio;
        c((a.re + a.im * ratio) / denom, (a.im - a.re * ratio) / denom)
    } else if abs_im >= abs_re {
        let ratio = b.re / b.im;
        let denom = b.re * ratio + b.im;
        c((a.re * ratio + a.im) / denom, (a.im * ratio - a.re) / denom)
    } else {
        c(f64::NAN, f64::NAN)
    }
}

/// The principal square root, with the special values of C99 Annex G.
pub(crate) fn sqrt(z: C) -> C {
    if z.im.is_infinite() {
        return c(f64::INFINITY, z.im);
    }
    if z.re.is_nan() || z.im.is_nan() {
        return if z.re == f64::INFINITY {
            c(z.re, f64::NAN)
        } else if z.re == f64::NEG_INFINITY {
            c(f64::NAN, f64::INFINITY)
        } else {
            c(f64::NAN, f64::NAN)
        };
    }
    if z.re.is_infinite() {
        return if z.re > 0.0 { c(z.re, 0.0f64.copysign(z.im)) } else { c(0.0, f64::INFINITY.copysign(z.im)) };
    }
    if z.re == 0.0 && z.im == 0.0 {
        return c(0.0, z.im);
    }
    let (ax, ay) = (z.re.abs(), z.im.abs());
    let s = if ax < f64::MIN_POSITIVE && ay < f64::MIN_POSITIVE {
        // hypot(ax, ay) would be subnormal, so scale up first.
        let ax = ldexp(ax, 53);
        ldexp((ax + ax.hypot(ldexp(ay, 53))).sqrt(), -27)
    } else {
        let ax = ax / 8.0;
        2.0 * (ax + ax.hypot(ay / 8.0)).sqrt()
    };
    let d = ay / (2.0 * s);
    if z.re >= 0.0 { c(s, d.copysign(z.im)) } else { c(d, s.copysign(z.im)) }
}

pub(crate) fn exp(z: C) -> C {
    if z.im == 0.0 {
        return c(z.re.exp(), z.im);
    }
    if z.re.is_infinite() && !z.im.is_finite() {
        return if z.re > 0.0 { c(z.re, f64::NAN) } else { c(0.0, 0.0) };
    }
    let (sin, cos) = z.im.sin_cos();
    if z.re > LOG_LARGE {
        let l = (z.re - 1.0).exp();
        c(l * cos * E, l * sin * E)
    } else {
        let l = z.re.exp();
        c(l * cos, l * sin)
    }
}

/// The real part scales parts whose `hypot` would overflow or be subnormal, and uses `ln_1p`
/// near the unit circle, where `ln` of the magnitude would cancel.
pub(crate) fn log(z: C) -> C {
    let (ax, ay) = (z.re.abs(), z.im.abs());
    let re = if ax > LARGE || ay > LARGE {
        (ax / 2.0).hypot(ay / 2.0).ln() + LN_2
    } else if ax < f64::MIN_POSITIVE && ay < f64::MIN_POSITIVE {
        if ax == 0.0 && ay == 0.0 {
            f64::NEG_INFINITY
        } else {
            ldexp(ax, 53).hypot(ldexp(ay, 53)).ln() - 53.0 * LN_2
        }
    } else {
        let m = ax.hypot(ay);
        if (0.71..=1.73).contains(&m) {
            let (big, small) = (ax.max(ay), ax.min(ay));
            ((big - 1.0) * (big + 1.0) + small * small).ln_1p() / 2.0
        } else {
            m.ln()
        }
    };
    c(re, z.im.atan2(z.re))
}

pub(crate) fn sin(z: C) -> C {
    let (sin, cos) = z.re.sin_cos();
    c(sin * z.im.cosh(), cos * z.im.sinh())
}

pub(crate) fn cos(z: C) -> C {
    let (sin, cos) = z.re.sin_cos();
    c(cos * z.im.cosh(), -(sin * z.im.sinh()))
}

/// `-i·tanh(iz)`.
pub(crate) fn tan(z: C) -> C {
    let t = tanh(c(-z.im, z.re));
    c(t.im, -t.re)
}

/// Kahan's, which stays accurate near the poles, where `sinh / cosh` would cancel.
fn tanh(z: C) -> C {
    if z.re.abs() > LOG_LARGE {
        return c(1.0f64.copysign(z.re), 4.0 * z.im.sin() * z.im.cos() * (-2.0 * z.re.abs()).exp());
    }
    let (tx, ty, cx) = (z.re.tanh(), z.im.tan(), 1.0 / z.re.cosh());
    let txty = tx * ty;
    let denom = 1.0 + txty * txty;
    c(tx * (1.0 + ty * ty) / denom, ty / denom * cx * cx)
}

pub(crate) fn asin(z: C) -> C {
    let s = asinh(c(-z.im, z.re));
    c(s.im, -s.re)
}

pub(crate) fn acos(z: C) -> C {
    if z.re.abs() > LARGE || z.im.abs() > LARGE {
        let re = z.im.abs().atan2(z.re);
        let l = (z.re / 2.0).hypot(z.im / 2.0).ln() + LN_2 * 2.0;
        let im = if z.re < 0.0 { -l.copysign(z.im) } else { l.copysign(-z.im) };
        return c(re, im);
    }
    let s1 = sqrt(c(1.0 - z.re, -z.im));
    let s2 = sqrt(c(1.0 + z.re, z.im));
    c(2.0 * s1.re.atan2(s2.re), (s2.re * s1.im - s2.im * s1.re).asinh())
}

pub(crate) fn atan(z: C) -> C {
    let s = atanh(c(-z.im, z.re));
    c(s.im, -s.re)
}

fn asinh(z: C) -> C {
    if z.re.abs() > LARGE || z.im.abs() > LARGE {
        let l = (z.re / 2.0).hypot(z.im / 2.0).ln() + LN_2 * 2.0;
        let re = if z.im >= 0.0 { l.copysign(z.re) } else { -l.copysign(-z.re) };
        return c(re, z.im.atan2(z.re.abs()));
    }
    let s1 = sqrt(c(1.0 + z.im, -z.re));
    let s2 = sqrt(c(1.0 - z.im, z.re));
    c((s1.re * s2.im - s2.re * s1.im).asinh(), z.im.atan2(s1.re * s2.re - s1.im * s2.im))
}

fn atanh(z: C) -> C {
    if z.re < 0.0 {
        let s = atanh(c(-z.re, -z.im));
        return c(-s.re, -s.im);
    }
    let ay = z.im.abs();
    if z.re > SQRT_LARGE || ay > SQRT_LARGE {
        let h = (z.re / 2.0).hypot(z.im / 2.0);
        return c(z.re / 4.0 / h / h, -FRAC_PI_2.copysign(-z.im));
    }
    if z.re == 1.0 && ay < SQRT_MIN {
        if ay == 0.0 {
            return c(f64::INFINITY, z.im);
        }
        return c(-(ay.sqrt() / ay.hypot(2.0).sqrt()).ln(), (2.0f64.atan2(-ay) / 2.0).copysign(z.im));
    }
    let re = (4.0 * z.re / ((1.0 - z.re) * (1.0 - z.re) + ay * ay)).ln_1p() / 4.0;
    let im = -(-2.0 * z.im).atan2((1.0 - z.re) * (1.0 + z.re) - ay * ay) / 2.0;
    c(re, im)
}
