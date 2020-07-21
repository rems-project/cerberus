#include <stdint.h>
#include <math.h>

double fabs(double x)
{
  union {double f; uint64_t i;} u = {x};
  u.i &= -1ULL/2;
  return u.f;
}

double scalbn(double x, int n)
{
  union {double f; uint64_t i;} u;
  double_t y = x;

  if (n > 1023) {
    y *= 0x1p1023;
    n -= 1023;
    if (n > 1023) {
      y *= 0x1p1023;
      n -= 1023;
      if (n > 1023)
        n = 1023;
    }
  } else if (n < -1022) {
    /* make sure final n < -53 to avoid double
       rounding in the subnormal range */
    y *= 0x1p-1022 * 0x1p53;
    n += 1022 - 53;
    if (n < -1022) {
      y *= 0x1p-1022 * 0x1p53;
      n += 1022 - 53;
      if (n < -1022)
        n = -1022;
    }
  }
  u.i = (uint64_t)(0x3ff+n)<<52;
  x = y * u.f;
  return x;
}

float scalbnf(float x, int n)
{
  union {float f; uint32_t i;} u;
  float_t y = x;

  if (n > 127) {
    y *= 0x1p127f;
    n -= 127;
    if (n > 127) {
      y *= 0x1p127f;
      n -= 127;
      if (n > 127)
        n = 127;
    }
  } else if (n < -126) {
    y *= 0x1p-126f * 0x1p24f;
    n += 126 - 24;
    if (n < -126) {
      y *= 0x1p-126f * 0x1p24f;
      n += 126 - 24;
      if (n < -126)
        n = -126;
    }
  }
  u.i = (uint32_t)(0x7f+n)<<23;
  x = y * u.f;
  return x;
}

#if LDBL_MANT_DIG == 53 && LDBL_MAX_EXP == 1024
long double scalbnl(long double x, int n)
{
	return scalbn(x, n);
}
#elif (LDBL_MANT_DIG == 64 || LDBL_MANT_DIG == 113) && LDBL_MAX_EXP == 16384
long double scalbnl(long double x, int n)
{
	union ldshape u;

	if (n > 16383) {
		x *= 0x1p16383L;
		n -= 16383;
		if (n > 16383) {
			x *= 0x1p16383L;
			n -= 16383;
			if (n > 16383)
				n = 16383;
		}
	} else if (n < -16382) {
		x *= 0x1p-16382L * 0x1p113L;
		n += 16382 - 113;
		if (n < -16382) {
			x *= 0x1p-16382L * 0x1p113L;
			n += 16382 - 113;
			if (n < -16382)
				n = -16382;
		}
	}
	u.f = 1.0;
	u.i.se = 0x3fff + n;
	return x * u.f;
}
#endif

/* Get two 32 bit ints from a double.  */
#define EXTRACT_WORDS(hi,lo,d)                    \
do {                                              \
  union {double f; uint64_t i;} __u;              \
  __u.f = (d);                                    \
  (hi) = __u.i >> 32;                             \
  (lo) = (uint32_t)__u.i;                         \
} while (0)

/* Set a double from two 32 bit ints.  */
#define INSERT_WORDS(d,hi,lo)                     \
do {                                              \
  union {double f; uint64_t i;} __u;              \
  __u.i = ((uint64_t)(hi)<<32) | (uint32_t)(lo);  \
  (d) = __u.f;                                    \
} while (0)


static const double tiny = 1.0e-300;

double sqrt(double x)
{
  double z;
  int32_t sign = (int)0x80000000;
  int32_t ix0,s0,q,m,t,i;
  uint32_t r,t1,s1,ix1,q1;

  EXTRACT_WORDS(ix0, ix1, x);

  /* take care of Inf and NaN */
  if ((ix0&0x7ff00000) == 0x7ff00000) {
    return x*x + x;  /* sqrt(NaN)=NaN, sqrt(+inf)=+inf, sqrt(-inf)=sNaN */
  }
  /* take care of zero */
  if (ix0 <= 0) {
    if (((ix0&~sign)|ix1) == 0)
      return x;  /* sqrt(+-0) = +-0 */
    if (ix0 < 0)
      return (x-x)/(x-x);  /* sqrt(-ve) = sNaN */
  }
  /* normalize x */
  m = ix0>>20;
  if (m == 0) {  /* subnormal x */
    while (ix0 == 0) {
      m -= 21;
      ix0 |= (ix1>>11);
      ix1 <<= 21;
    }
    for (i=0; (ix0&0x00100000) == 0; i++)
      ix0<<=1;
    m -= i - 1;
    ix0 |= ix1>>(32-i);
    ix1 <<= i;
  }
  m -= 1023;    /* unbias exponent */
  ix0 = (ix0&0x000fffff)|0x00100000;
  if (m & 1) {  /* odd m, double x to make it even */
    ix0 += ix0 + ((ix1&sign)>>31);
    ix1 += ix1;
  }
  m >>= 1;      /* m = [m/2] */

  /* generate sqrt(x) bit by bit */
  ix0 += ix0 + ((ix1&sign)>>31);
  ix1 += ix1;
  q = q1 = s0 = s1 = 0;  /* [q,q1] = sqrt(x) */
  r = 0x00200000;        /* r = moving bit from right to left */

  while (r != 0) {
    t = s0 + r;
    if (t <= ix0) {
      s0   = t + r;
      ix0 -= t;
      q   += r;
    }
    ix0 += ix0 + ((ix1&sign)>>31);
    ix1 += ix1;
    r >>= 1;
  }

  r = sign;
  while (r != 0) {
    t1 = s1 + r;
    t  = s0;
    if (t < ix0 || (t == ix0 && t1 <= ix1)) {
      s1 = t1 + r;
      if ((t1&sign) == sign && (s1&sign) == 0)
        s0++;
      ix0 -= t;
      if (ix1 < t1)
        ix0--;
      ix1 -= t1;
      q1 += r;
    }
    ix0 += ix0 + ((ix1&sign)>>31);
    ix1 += ix1;
    r >>= 1;
  }

  /* use floating add to find out rounding direction */
  if ((ix0|ix1) != 0) {
    z = 1.0 - tiny; /* raise inexact flag */
    if (z >= 1.0) {
      z = 1.0 + tiny;
      if (q1 == (uint32_t)0xffffffff) {
        q1 = 0;
        q++;
      } else if (z > 1.0) {
        if (q1 == (uint32_t)0xfffffffe)
          q++;
        q1 += 2;
      } else
        q1 += q1 & 1;
    }
  }
  ix0 = (q>>1) + 0x3fe00000;
  ix1 = q1>>1;
  if (q&1)
    ix1 |= sign;
  ix0 += m << 20;
  INSERT_WORDS(z, ix0, ix1);
  return z;
}