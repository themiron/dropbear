/*
 * Dropbear - a SSH2 server
 * 
 * Copyright (c) 2002,2003 Matt Johnston
 * All rights reserved.
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE. */

#include "includes.h"
#include "dbrandom.h"
#include "curve25519.h"

#if DROPBEAR_CURVE448

/* Modified The wolfSSL embedded SSL library (formerly CyaSSL).
 * https://www.wolfssl.com/ */

/* Normalize the field element.
 * Ensure result is in range: 0..2^448-2^224-2
 *
 * a  [in]  Field element in range 0..2^448-1.
 */
static void fe448_norm(uint8_t* a)
{
    int i;
    int16_t c = 0;
    int16_t o = 0;

    for (i = 0; i < 56; i++) {
        c += a[i];
        if ((i == 0) || (i == 28))
            c += 1;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += a[i];
        a[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Copy one field element into another: d = a.
 *
 * d  [in]  Destination field element.
 * a  [in]  Source field element.
 */
static void fe448_copy(uint8_t* d, const uint8_t* a)
{
    int i;
    for (i = 0; i < 56; i++) {
         d[i] = a[i];
    }
}

/* Conditionally swap the elements.
 * Constant time implementation.
 *
 * a  [in]  First field element.
 * b  [in]  Second field element.
 * c  [in]  Swap when 1. Valid values: 0, 1.
 */
static void fe448_cswap(uint8_t* a, uint8_t* b, int c)
{
    int i;
    uint8_t mask = -(uint8_t)c;
    uint8_t t[56];

    for (i = 0; i < 56; i++)
        t[i] = (a[i] ^ b[i]) & mask;
    for (i = 0; i < 56; i++)
        a[i] ^= t[i];
    for (i = 0; i < 56; i++)
        b[i] ^= t[i];
}

/* Add two field elements. r = (a + b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold sum.
 * a  [in]  Field element to add.
 * b  [in]  Field element to add.
 */
static void fe448_add(uint8_t* r, const uint8_t* a, const uint8_t* b)
{
    int i;
    int16_t c = 0;
    int16_t o = 0;

    for (i = 0; i < 56; i++) {
        c += a[i];
        c += b[i];
        r[i] = (uint8_t)c;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += r[i];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Subtract a field element from another. r = (a - b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold difference.
 * a  [in]  Field element to subtract from.
 * b  [in]  Field element to subtract.
 */
static void fe448_sub(uint8_t* r, const uint8_t* a, const uint8_t* b)
{
    int i;
    int16_t c = 0;
    int16_t o = 0;

    for (i = 0; i < 56; i++) {
        if (i == 28)
            c += 0x1fc;
        else
            c += 0x1fe;
        c += a[i];
        c -= b[i];
        r[i] = (uint8_t)c;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += r[i];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Mulitply a field element by 39081. r = (39081 * a) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 */
static void fe448_mul39081(uint8_t* r, const uint8_t* a)
{
    int i;
    int32_t c = 0;
    int32_t o = 0;

    for (i = 0; i < 56; i++) {
        c += a[i] * (int32_t)39081;
        r[i] = (uint8_t)c;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += r[i];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Mulitply two field elements. r = (a * b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 * b  [in]  Field element to multiply.
 */
static void fe448_mul(uint8_t* r, const uint8_t* a, const uint8_t* b)
{
    int i, k;
    int32_t c = 0;
    int16_t o = 0, cc = 0;
    uint8_t t[112];

    for (k = 0; k < 56; k++) {
        i = 0;
        for (; i <= k; i++) {
            c += (int32_t)a[i] * b[k - i];
        }
        t[k] = (uint8_t)c;
        c >>= 8;
    }
    for (; k < 111; k++) {
        i = k - 55;
        for (; i < 56; i++) {
            c += (int32_t)a[i] * b[k - i];
        }
        t[k] = (uint8_t)c;
        c >>= 8;
    }
    t[k] = (uint8_t)c;

    for (i = 0; i < 28; i++) {
        o += t[i];
        o += t[i + 56];
        o += t[i + 84];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
    for (i = 28; i < 56; i++) {
        o += t[i];
        o += t[i + 56];
        o += t[i + 28];
        o += t[i + 56];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) cc += o;
        cc += r[i];
        r[i] = (uint8_t)cc;
        cc >>= 8;
    }
}

/* Square a field element. r = (a * a) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to square.
 */
static void fe448_sqr(uint8_t* r, const uint8_t* a)
{
    int i, k;
    int32_t c = 0;
    int32_t p;
    int16_t o = 0, cc = 0;
    uint8_t t[112];

    for (k = 0; k < 56; k++) {
        i = 0;
        for (; i <= k; i++) {
            if (k - i < i)
                break;
            p = (int32_t)a[i] * a[k - i];
            if (k - i != i)
                p *= 2;
            c += p;
        }
        t[k] = (uint8_t)c;
        c >>= 8;
    }
    for (; k < 111; k++) {
         i = k - 55;
        for (; i < 56; i++) {
            if (k - i < i)
                break;
            p = (int32_t)a[i] * a[k - i];
            if (k - i != i)
                p *= 2;
            c += p;
        }
        t[k] = (uint8_t)c;
        c >>= 8;
    }
    t[k] = (uint8_t)c;

    for (i = 0; i < 28; i++) {
        o += t[i];
        o += t[i + 56];
        o += t[i + 84];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
    for (i = 28; i < 56; i++) {
        o += t[i];
        o += t[i + 56];
        o += t[i + 28];
        o += t[i + 56];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) cc += o;
        cc += r[i];
        r[i] = (uint8_t)cc;
        cc >>= 8;
    }
    fe448_norm(r);
}

/* Invert the field element. (r * a) mod (2^448 - 2^224 - 1) = 1
 * Constant time implementation - using Fermat's little theorem:
 *   a^(p-1) mod p = 1 => a^(p-2) mod p = 1/a
 * For curve448: p - 2 = 2^448 - 2^224 - 3
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to invert.
 */
static void fe448_invert(uint8_t* r, const uint8_t* a)
{
    int i;
    uint8_t t[56];

    fe448_sqr(t, a);
    fe448_mul(t, t, a);
    for (i = 0; i < 221; i++) {
        fe448_sqr(t, t);
        fe448_mul(t, t, a);
    }
    fe448_sqr(t, t);
    for (i = 0; i < 222; i++) {
        fe448_sqr(t, t);
        fe448_mul(t, t, a);
    }
    fe448_sqr(t, t);
    fe448_sqr(t, t);
    fe448_mul(r, t, a);
}

/* Scalar multiply the point by a number. r = n.a
 * Uses Montogmery ladder and only requires the x-ordinate.
 *
 * r  [in]  Field element to hold result.
 * n  [in]  Scalar as an array of bytes.
 * a  [in]  Point to multiply - x-ordinate only.
 */
static void curve448(uint8_t* r, const uint8_t* n, const uint8_t* a)
{
    uint8_t x1[56];
    uint8_t x2[56] = {1};
    uint8_t z2[56] = {0};
    uint8_t x3[56];
    uint8_t z3[56] = {1};
    uint8_t t0[56];
    uint8_t t1[56];
    int i;
    unsigned int swap;
    unsigned int b;

    fe448_copy(x1, a);
    fe448_copy(x3, a);

    swap = 0;
    for (i = 447; i >= 0; --i) {
        b = (n[i >> 3] >> (i & 7)) & 1;
        swap ^= b;
        fe448_cswap(x2, x3, swap);
        fe448_cswap(z2, z3, swap);
        swap = b;

        /* Montgomery Ladder - double and add */
        fe448_add(t0, x2, z2);
        fe448_add(t1, x3, z3);
        fe448_sub(x2, x2, z2);
        fe448_sub(x3, x3, z3);
        fe448_mul(t1, t1, x2);
        fe448_mul(z3, x3, t0);
        fe448_sqr(t0, t0);
        fe448_sqr(x2, x2);
        fe448_add(x3, z3, t1);
        fe448_sqr(x3, x3);
        fe448_sub(z3, z3, t1);
        fe448_sqr(z3, z3);
        fe448_mul(z3, z3, x1);
        fe448_sub(t1, t0, x2);
        fe448_mul(x2, t0, x2);
        fe448_mul39081(z2, t1);
        fe448_add(z2, t0, z2);
        fe448_mul(z2, z2, t1);
    }
    fe448_cswap(x2, x3, swap);
    fe448_cswap(z2, z3, swap);

    fe448_invert(z2, z2);
    fe448_mul(r, x2, z2);
    fe448_norm(r);
}

void dropbear_curve448_scalarmult(unsigned char *q, const unsigned char *n, const unsigned char *p)
{
    uint8_t z[56];

    fe448_copy(z, n);
    z[0] &= 0xfc;
    z[55] |= 0x80;
    curve448(q, z, p);
}

#endif /* DROPBEAR_CURVE448 */
