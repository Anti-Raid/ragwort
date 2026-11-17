//! Complex arithmetic on pairs of `f64`. The square root, the exponential and the inverse
//! functions follow CPython's `cmath`. CPython takes them from Kahan's "Branch Cuts for Complex
//! Elementary Functions". As a result, a signed zero lands on the correct side of each branch cut.

use std::f64::consts::{FRAC_PI_2, LN_2};

#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) struct C {
    pub re: f64,
    pub im: f64,
}

const fn c(re: f64, im: f64) -> C {
    C { re, im }
}

const LARGE: f64 = f64::MAX / 4.0;
/// `ln(LARGE)`. `exp` overflows for arguments a little larger than this.
const LOG_LARGE: f64 = 708.3964185322641;
/// `sqrt(LARGE)`.
const SQRT_LARGE: f64 = 6.703903964971299e153;
/// `sqrt(f64::MIN_POSITIVE)`.
const SQRT_MIN: f64 = 1.4916681462400413e-154;

/// Returns `x * 2^exponent`. The result is rounded only once, unless it is far below the normal range.
pub(crate) fn ldexp(mut x: f64, exponent: i64) -> f64 {
    let mut exponent = exponent.clamp(-2200, 2200);
    #[inline(always)]
    fn power(exponent: i64) -> f64 {
        f64::from_bits(((exponent + 1023) as u64) << 52)
    }
    while exponent > 1023 {
        x *= power(1023);
        exponent -= 1023;
    }
    while exponent < -1022 {
        x *= power(-1022);
        exponent += 1022;
    }
    x * power(exponent)
}

/// Returns `a / b` by Smith's method, as CPython computes it.
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

/// Returns the principal square root of `z`, with the special values of C99 Annex G.
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
    // `root` is `sqrt((ax + hypot(ax, ay)) / 2)` and `quotient` is `ay / (2 * root)`. For `z.re >= 0` the result is `root + quotient·i`.
    // For `z.re < 0` the two swap places. In both cases the imaginary part takes the sign of `z.im`.
    // Each branch scales the parts first, so that `ax + hypot(ax, ay)` neither overflows nor becomes subnormal.
    // With `t = ax + hypot(ax, ay)`, dividing the parts by 8 gives `2 * sqrt(t / 8) = sqrt(t / 2)`.
    // Multiplying the parts by 2^53 gives `sqrt(2^53 * t) * 2^-27 = sqrt(t / 2)`.
    let root = if ax < f64::MIN_POSITIVE && ay < f64::MIN_POSITIVE {
        // `hypot(ax, ay)` can be subnormal here, so scale both parts up by 2^53 first.
        let ax = ldexp(ax, 53);
        ldexp((ax + ax.hypot(ldexp(ay, 53))).sqrt(), -27)
    } else {
        let ax = ax / 8.0;
        2.0 * (ax + ax.hypot(ay / 8.0)).sqrt()
    };
    let quotient = ay / (2.0 * root);
    if z.re >= 0.0 { c(root, quotient.copysign(z.im)) } else { c(quotient, root.copysign(z.im)) }
}

/// Returns `factor · e^x`. The result overflows only when the product itself overflows. A zero `factor` is returned unchanged, even when `e^x` overflows.
fn times_exp(factor: f64, x: f64) -> f64 {
    if factor == 0.0 {
        factor
    } else if x <= LOG_LARGE {
        factor * x.exp()
    } else {
        let half = (x / 2.0).exp();
        factor * half * half
    }
}

pub(crate) fn exp(z: C) -> C {
    if z.im == 0.0 {
        return c(z.re.exp(), z.im);
    }
    if z.re.is_infinite() && !z.im.is_finite() {
        return if z.re > 0.0 { c(z.re, f64::NAN) } else { c(0.0, 0.0) };
    }
    let (sin, cos) = z.im.sin_cos();
    c(times_exp(cos, z.re), times_exp(sin, z.re))
}

/// Returns the principal natural logarithm of `z`. The real part is `ln |z|`. It scales the parts when their `hypot` would overflow
/// or be subnormal. Near the unit circle it uses `ln_1p`, because `ln` of the magnitude would lose precision there.
pub(crate) fn log(z: C) -> C {
    let (ax, ay) = (z.re.abs(), z.im.abs());
    let re = if ax > LARGE || ay > LARGE {
        // `hypot(ax, ay)` could overflow. Halve the parts first, then add `ln 2` to the logarithm.
        (ax / 2.0).hypot(ay / 2.0).ln() + LN_2
    } else if ax < f64::MIN_POSITIVE && ay < f64::MIN_POSITIVE {
        if ax == 0.0 && ay == 0.0 {
            f64::NEG_INFINITY
        } else {
            // `hypot(ax, ay)` can be subnormal. Scale the parts up by 2^53 first, then subtract `ln(2^53)` from the logarithm.
            ldexp(ax, 53).hypot(ldexp(ay, 53)).ln() - 53.0 * LN_2
        }
    } else {
        let magnitude = ax.hypot(ay);
        if (0.71..=1.73).contains(&magnitude) {
            // The magnitude is close to 1, where `ln` loses precision. Use `ln |z| = ln_1p(|z|² - 1) / 2` instead.
            // `|z|² - 1` is computed as `(big - 1)(big + 1) + small²`, which avoids the cancellation in `big² + small² - 1`.
            let (big, small) = (ax.max(ay), ax.min(ay));
            ((big - 1.0) * (big + 1.0) + small * small).ln_1p() / 2.0
        } else {
            magnitude.ln()
        }
    };
    c(re, z.im.atan2(z.re))
}

/// Returns `sin(z)`, computed as `-i·sinh(iz)`.
pub(crate) fn sin(z: C) -> C {
    let rotated = sinh(c(-z.im, z.re));
    c(rotated.im, -rotated.re)
}

/// Returns `cos(z)`, computed as `cosh(iz)`.
pub(crate) fn cos(z: C) -> C {
    cosh(c(-z.im, z.re))
}

/// Returns `tan(z)`, computed as `-i·tanh(iz)`.
pub(crate) fn tan(z: C) -> C {
    let rotated = tanh(c(-z.im, z.re));
    c(rotated.im, -rotated.re)
}

/// Returns `factor · sinh(x)` if `odd`, or `factor · cosh(x)` otherwise. This is for `|x|` so large that `sinh` and `cosh` alone would overflow. Both are then `±e^|x| / 2`.
fn times_half_exp(factor: f64, x: f64, odd: bool) -> f64 {
    let result = times_exp(factor / 2.0, x.abs());
    if odd && x < 0.0 { -result } else { result }
}

fn sinh(z: C) -> C {
    let (x, y) = (z.re, z.im);
    if !x.is_finite() || !y.is_finite() {
        return if x.is_infinite() && y.is_finite() {
            if y == 0.0 { z } else { c(x * y.cos(), f64::INFINITY * y.sin()) }
        } else if x.is_infinite() || x == 0.0 || x.is_nan() && y == 0.0 {
            c(x, if x.is_nan() { y } else { f64::NAN })
        } else {
            c(f64::NAN, f64::NAN)
        };
    }
    let (sin, cos) = y.sin_cos();
    if x.abs() <= LOG_LARGE {
        c(cos * x.sinh(), sin * x.cosh())
    } else {
        c(times_half_exp(cos, x, true), times_half_exp(sin, x, false))
    }
}

fn cosh(z: C) -> C {
    let (x, y) = (z.re, z.im);
    if !x.is_finite() || !y.is_finite() {
        return if x.is_infinite() && y.is_finite() {
            if y == 0.0 { c(f64::INFINITY, y * x.signum()) } else { c(f64::INFINITY * y.cos(), x * y.sin()) }
        } else if x.is_infinite() {
            c(f64::INFINITY, f64::NAN)
        } else if x == 0.0 || x.is_nan() && y == 0.0 {
            c(f64::NAN, if x.is_nan() { 0.0 } else { x })
        } else {
            c(f64::NAN, f64::NAN)
        };
    }
    let (sin, cos) = y.sin_cos();
    if x.abs() <= LOG_LARGE {
        c(cos * x.cosh(), sin * x.sinh())
    } else {
        c(times_half_exp(cos, x, false), times_half_exp(sin, x, true))
    }
}

/// Returns `tanh(z)` by Kahan's formula. The formula stays accurate near the poles, where `sinh / cosh` would lose precision.
fn tanh(z: C) -> C {
    let (x, y) = (z.re, z.im);
    if !x.is_finite() || !y.is_finite() {
        return if x.is_infinite() {
            c(1.0f64.copysign(x), 0.0f64.copysign(if y.is_finite() { y.sin() * y.cos() } else { y }))
        } else if x == 0.0 || x.is_nan() && y == 0.0 {
            c(x, if x.is_nan() { y } else { f64::NAN })
        } else {
            c(f64::NAN, f64::NAN)
        };
    }
    if x.abs() > LOG_LARGE {
        return c(1.0f64.copysign(x), 4.0 * y.sin() * y.cos() * (-2.0 * x.abs()).exp());
    }
    let (tx, ty, cx) = (x.tanh(), y.tan(), 1.0 / x.cosh());
    let txty = tx * ty;
    let denom = 1.0 + txty * txty;
    c(tx * (1.0 + ty * ty) / denom, ty / denom * cx * cx)
}

pub(crate) fn asin(z: C) -> C {
    let rotated = asinh(c(-z.im, z.re));
    c(rotated.im, -rotated.re)
}

pub(crate) fn acos(z: C) -> C {
    if z.re.is_nan() || z.im.is_nan() {
        return if z.re.is_infinite() {
            c(f64::NAN, f64::INFINITY)
        } else if z.im.is_infinite() {
            c(f64::NAN, -z.im)
        } else if z.re == 0.0 {
            c(FRAC_PI_2, f64::NAN)
        } else {
            c(f64::NAN, f64::NAN)
        };
    }
    if z.re.abs() > LARGE || z.im.abs() > LARGE {
        let re = z.im.abs().atan2(z.re);
        let log_magnitude = (z.re / 2.0).hypot(z.im / 2.0).ln() + LN_2 * 2.0;
        let im = if z.re < 0.0 { -log_magnitude.copysign(z.im) } else { log_magnitude.copysign(-z.im) };
        return c(re, im);
    }
    let s1 = sqrt(c(1.0 - z.re, -z.im));
    let s2 = sqrt(c(1.0 + z.re, z.im));
    c(2.0 * s1.re.atan2(s2.re), (s2.re * s1.im - s2.im * s1.re).asinh())
}

pub(crate) fn atan(z: C) -> C {
    let rotated = atanh(c(-z.im, z.re));
    c(rotated.im, -rotated.re)
}

fn asinh(z: C) -> C {
    if z.re.is_nan() || z.im.is_nan() {
        return if z.re.is_infinite() {
            c(z.re, f64::NAN)
        } else if z.im.is_infinite() {
            c(f64::INFINITY, f64::NAN)
        } else if z.re.is_nan() && z.im == 0.0 {
            z
        } else {
            c(f64::NAN, f64::NAN)
        };
    }
    if z.re.abs() > LARGE || z.im.abs() > LARGE {
        let log_magnitude = (z.re / 2.0).hypot(z.im / 2.0).ln() + LN_2 * 2.0;
        let re = if z.im >= 0.0 { log_magnitude.copysign(z.re) } else { -log_magnitude.copysign(-z.re) };
        return c(re, z.im.atan2(z.re.abs()));
    }
    let s1 = sqrt(c(1.0 + z.im, -z.re));
    let s2 = sqrt(c(1.0 - z.im, z.re));
    c((s1.re * s2.im - s2.re * s1.im).asinh(), z.im.atan2(s1.re * s2.re - s1.im * s2.im))
}

fn atanh(z: C) -> C {
    if z.re.is_nan() || z.im.is_nan() {
        return if z.re.is_infinite() {
            c(0.0f64.copysign(z.re), f64::NAN)
        } else if z.im.is_infinite() {
            c(0.0, FRAC_PI_2.copysign(z.im))
        } else if z.re == 0.0 {
            c(z.re, f64::NAN)
        } else {
            c(f64::NAN, f64::NAN)
        };
    }
    if z.re < 0.0 {
        let negated = atanh(c(-z.re, -z.im));
        return c(-negated.re, -negated.im);
    }
    let ay = z.im.abs();
    if z.re > SQRT_LARGE || ay > SQRT_LARGE {
        let half_magnitude = (z.re / 2.0).hypot(z.im / 2.0);
        let re = if half_magnitude.is_infinite() { 0.0f64.copysign(z.re) } else { z.re / 4.0 / half_magnitude / half_magnitude };
        return c(re, -FRAC_PI_2.copysign(-z.im));
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
