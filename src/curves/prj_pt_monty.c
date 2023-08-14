/*
 *  Copyright (C) 2017 - This file is part of libecc project
 *
 *  Authors:
 *      Ryad BENADJILA <ryadbenadjila@gmail.com>
 *      Arnaud EBALARD <arnaud.ebalard@ssi.gouv.fr>
 *      Jean-Pierre FLORI <jean-pierre.flori@ssi.gouv.fr>
 *
 *  Contributors:
 *      Nicolas VIVET <nicolas.vivet@ssi.gouv.fr>
 *      Karim KHALFALLAH <karim.khalfallah@ssi.gouv.fr>
 *
 *  This software is licensed under a dual BSD and GPL v2 license.
 *  See LICENSE file at the root folder of the project.
 */
#include "ec_shortw.h"
#include "prj_pt.h"
#include "prj_pt_monty.h"
#include "../nn/nn_logical.h"
#include "../nn/nn_add.h"
#include "../nn/nn_rand.h"
#include "../fp/fp_add.h"
#include "../fp/fp_mul.h"
#include "../fp/fp_montgomery.h"
#include "../fp/fp_rand.h"

#include "../utils/dbg_sig.h"

/*
 * If NO_USE_COMPLETE_FORMULAS flag is not defined addition formulas from Algorithm 1
 * of https://joostrenes.nl/publications/complete.pdf are used, otherwise
 * http://www.hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#addition-add-1998-cmo-2
 */
static void __prj_pt_add_monty(prj_pt_t out, prj_pt_src_t in1,
			       prj_pt_src_t in2)
{
#ifndef NO_USE_COMPLETE_FORMULAS
	fp t0, t1, t2, t3, t4, t5;

	/* Info: initialization check of in1 and in2 done at upper level */
	MUST_HAVE(in1->crv == in2->crv);

	prj_pt_init(out, in1->crv);

	fp_init(&t0, out->crv->a.ctx);
	fp_init(&t1, out->crv->a.ctx);
	fp_init(&t2, out->crv->a.ctx);
	fp_init(&t3, out->crv->a.ctx);
	fp_init(&t4, out->crv->a.ctx);
	fp_init(&t5, out->crv->a.ctx);

	MUST_HAVE(out->crv == in1->crv);
	MUST_HAVE(out->crv == in2->crv);

	fp_mul_monty(&t0, &in1->X, &in2->X);
	fp_mul_monty(&t1, &in1->Y, &in2->Y);
	fp_mul_monty(&t2, &in1->Z, &in2->Z);
	fp_add_monty(&t3, &in1->X, &in1->Y);
	fp_add_monty(&t4, &in2->X, &in2->Y);

	fp_mul_monty(&t3, &t3, &t4);
	fp_add_monty(&t4, &t0, &t1);
	fp_sub_monty(&t3, &t3, &t4);
	fp_add_monty(&t4, &in1->X, &in1->Z);
	fp_add_monty(&t5, &in2->X, &in2->Z);

	fp_mul_monty(&t4, &t4, &t5);
	fp_add_monty(&t5, &t0, &t2);
	fp_sub_monty(&t4, &t4, &t5);
	fp_add_monty(&t5, &in1->Y, &in1->Z);
	fp_add_monty(&out->X, &in2->Y, &in2->Z);

	fp_mul_monty(&t5, &t5, &out->X);
	fp_add_monty(&out->X, &t1, &t2);
	fp_sub_monty(&t5, &t5, &out->X);
	fp_mul_monty(&out->Z, &in1->crv->a_monty, &t4);
	fp_mul_monty(&out->X, &in1->crv->b3_monty, &t2);

	fp_add_monty(&out->Z, &out->X, &out->Z);
	fp_sub_monty(&out->X, &t1, &out->Z);
	fp_add_monty(&out->Z, &t1, &out->Z);
	fp_mul_monty(&out->Y, &out->X, &out->Z);
	fp_add_monty(&t1, &t0, &t0);

	fp_add_monty(&t1, &t1, &t0);
	fp_mul_monty(&t2, &in1->crv->a_monty, &t2);
	fp_mul_monty(&t4, &in1->crv->b3_monty, &t4);
	fp_add_monty(&t1, &t1, &t2);
	fp_sub_monty(&t2, &t0, &t2);

	fp_mul_monty(&t2, &in1->crv->a_monty, &t2);
	fp_add_monty(&t4, &t4, &t2);
	fp_mul_monty(&t0, &t1, &t4);
	fp_add_monty(&out->Y, &out->Y, &t0);
	fp_mul_monty(&t0, &t5, &t4);

	fp_mul_monty(&out->X, &t3, &out->X);
	fp_sub_monty(&out->X, &out->X, &t0);
	fp_mul_monty(&t0, &t3, &t1);
	fp_mul_monty(&out->Z, &t5, &out->Z);
	fp_add_monty(&out->Z, &out->Z, &t0);

	fp_uninit(&t0);
	fp_uninit(&t1);
	fp_uninit(&t2);
	fp_uninit(&t3);
	fp_uninit(&t4);
	fp_uninit(&t5);
#else
	fp Y1Z2, X1Z2, Z1Z2, u, uu, v, vv, vvv, R, A;

	/* Info: in1 and in2 init check done in upper levels */
	MUST_HAVE(in1->crv == in2->crv);
	MUST_HAVE(!prj_pt_iszero(in1));
	MUST_HAVE(!prj_pt_iszero(in2));
	/*
	 * The following test which guarantees in1 and in2 are not
	 * equal or opposite needs to be rewritten because it
	 * has a *HUGE* impact on perf (ec_self_tests run on
	 * all test vectors takes 24 times as long with this
	 * enabled). The same exists in non monty version.
	 */
	SHOULD_HAVE(!prj_pt_eq_or_opp(in1, in2));

	prj_pt_init(out, in1->crv);

	fp_init(&Y1Z2, out->crv->a.ctx);
	fp_init(&X1Z2, out->crv->a.ctx);
	fp_init(&Z1Z2, out->crv->a.ctx);
	fp_init(&u, out->crv->a.ctx);
	fp_init(&uu, out->crv->a.ctx);
	fp_init(&v, out->crv->a.ctx);
	fp_init(&vv, out->crv->a.ctx);
	fp_init(&vvv, out->crv->a.ctx);
	fp_init(&R, out->crv->a.ctx);
	fp_init(&A, out->crv->a.ctx);

	/* Y1Z2 = Y1*Z2 */
	fp_mul_monty(&Y1Z2, &(in1->Y), &(in2->Z));

	/* X1Z2 = X1*Z2 */
	fp_mul_monty(&X1Z2, &(in1->X), &(in2->Z));

	/* Z1Z2 = Z1*Z2 */
	fp_mul_monty(&Z1Z2, &(in1->Z), &(in2->Z));

	/* u = Y2*Z1-Y1Z2 */
	fp_mul_monty(&u, &(in2->Y), &(in1->Z));
	fp_sub_monty(&u, &u, &Y1Z2);

	/* uu = u² */
	fp_sqr_monty(&uu, &u);

	/* v = X2*Z1-X1Z2 */
	fp_mul_monty(&v, &(in2->X), &(in1->Z));
	fp_sub_monty(&v, &v, &X1Z2);

	/* vv = v² */
	fp_sqr_monty(&vv, &v);

	/* vvv = v*vv */
	fp_mul_monty(&vvv, &v, &vv);

	/* R = vv*X1Z2 */
	fp_mul_monty(&R, &vv, &X1Z2);

	/* A = uu*Z1Z2-vvv-2*R */
	fp_mul_monty(&A, &uu, &Z1Z2);
	fp_sub_monty(&A, &A, &vvv);
	fp_sub_monty(&A, &A, &R);
	fp_sub_monty(&A, &A, &R);

	/* X3 = v*A */
	fp_mul_monty(&(out->X), &v, &A);

	/* Y3 = u*(R-A)-vvv*Y1Z2 */
	fp_sub_monty(&R, &R, &A);
	fp_mul_monty(&(out->Y), &u, &R);
	fp_mul_monty(&R, &vvv, &Y1Z2);
	fp_sub_monty(&(out->Y), &(out->Y), &R);

	/* Z3 = vvv*Z1Z2 */
	fp_mul_monty(&(out->Z), &vvv, &Z1Z2);

	fp_uninit(&Y1Z2);
	fp_uninit(&X1Z2);
	fp_uninit(&Z1Z2);
	fp_uninit(&u);
	fp_uninit(&uu);
	fp_uninit(&v);
	fp_uninit(&vv);
	fp_uninit(&vvv);
	fp_uninit(&R);
	fp_uninit(&A);
#endif
}

/* Aliased version */
static void _prj_pt_add_monty(prj_pt_t out, prj_pt_src_t in1, prj_pt_src_t in2)
{
	if ((out == in1) || (out == in2)) {
		prj_pt out_cpy;
		prj_pt_init(&out_cpy, out->crv);
		prj_pt_copy(&out_cpy, out);
		__prj_pt_add_monty(&out_cpy, in1, in2);
		prj_pt_copy(out, &out_cpy);
		prj_pt_uninit(&out_cpy);
	} else {
		__prj_pt_add_monty(out, in1, in2);
	}
}

/* Public version of the addition to handle the case where the inputs are
 * zero or opposites
 */
void prj_pt_add_monty(prj_pt_t out, prj_pt_src_t in1, prj_pt_src_t in2)
{
	prj_pt_check_initialized(in1);
	prj_pt_check_initialized(in2);

#ifdef NO_USE_COMPLETE_FORMULAS
	if (prj_pt_iszero(in1)) {
		prj_pt_init(out, in2->crv);
		prj_pt_copy(out, in2);
	} else if (prj_pt_iszero(in2)) {
		prj_pt_init(out, in1->crv);
		prj_pt_copy(out, in1);
	}
	/*
	 * The following test which guarantees in1 and in2 are not
	 * equal or opposite needs to be rewritten because it
	 * has a *HUGE* impact on perf (ec_self_tests run on
	 * all test vectors takes 24 times as long with this
	 * enabled). The same exists in non monty version.
	 */
	else if (prj_pt_eq_or_opp(in1, in2)) {
		if (prj_pt_cmp(in1, in2) == 0) {
			prj_pt_dbl_monty(out, in1);
		} else {
			prj_pt_init(out, in1->crv);
			prj_pt_zero(out);
		}
	} else {
		_prj_pt_add_monty(out, in1, in2);
	}
#else
	_prj_pt_add_monty(out, in1, in2);
#endif
}

/*
 * If NO_USE_COMPLETE_FORMULAS flag is not defined addition formulas from Algorithm 3
 * of https://joostrenes.nl/publications/complete.pdf are used, otherwise
 * http://www.hyperelliptic.org/EFD/g1p/auto-shortw-projective.html#doubling-dbl-2007-bl
 */
static void __prj_pt_dbl_monty(prj_pt_t out, prj_pt_src_t in)
{
#ifndef NO_USE_COMPLETE_FORMULAS
	fp t0, t1, t2 ,t3;

	/* Info: initialization check of in done at upper level */
	prj_pt_init(out, in->crv);

	fp_init(&t0, out->crv->a.ctx);
	fp_init(&t1, out->crv->a.ctx);
	fp_init(&t2, out->crv->a.ctx);
	fp_init(&t3, out->crv->a.ctx);

	MUST_HAVE(out->crv == in->crv);

	fp_mul_monty(&t0, &in->X, &in->X);
	fp_mul_monty(&t1, &in->Y, &in->Y);
	fp_mul_monty(&t2, &in->Z, &in->Z);
	fp_mul_monty(&t3, &in->X, &in->Y);
	fp_add_monty(&t3, &t3, &t3);

	fp_mul_monty(&out->Z, &in->X, &in->Z);
	fp_add_monty(&out->Z, &out->Z, &out->Z);
	fp_mul_monty(&out->X, &in->crv->a_monty, &out->Z);
	fp_mul_monty(&out->Y, &in->crv->b3_monty, &t2);
	fp_add_monty(&out->Y, &out->X, &out->Y);

	fp_sub_monty(&out->X, &t1, &out->Y);
	fp_add_monty(&out->Y, &t1, &out->Y);
	fp_mul_monty(&out->Y, &out->X, &out->Y);
	fp_mul_monty(&out->X, &t3, &out->X);
	fp_mul_monty(&out->Z, &in->crv->b3_monty, &out->Z);

	fp_mul_monty(&t2, &in->crv->a_monty, &t2);
	fp_sub_monty(&t3, &t0, &t2);
	fp_mul_monty(&t3, &in->crv->a_monty, &t3);
	fp_add_monty(&t3, &t3, &out->Z);
	fp_add_monty(&out->Z, &t0, &t0);

	fp_add_monty(&t0, &out->Z, &t0);
	fp_add_monty(&t0, &t0, &t2);
	fp_mul_monty(&t0, &t0, &t3);
	fp_add_monty(&out->Y, &out->Y, &t0);
	fp_mul_monty(&t2, &in->Y, &in->Z);

	fp_add_monty(&t2, &t2, &t2);
	fp_mul_monty(&t0, &t2, &t3);
	fp_sub_monty(&out->X, &out->X, &t0);
	fp_mul_monty(&out->Z, &t2, &t1);
	fp_add_monty(&out->Z, &out->Z, &out->Z);

	fp_add_monty(&out->Z, &out->Z, &out->Z);

	fp_uninit(&t0);
	fp_uninit(&t1);
	fp_uninit(&t2);
	fp_uninit(&t3);
#else
	fp XX, ZZ, w, s, ss, sss, R, RR, B, h;

	/* Info: in init check done in upper levels */
	MUST_HAVE(!prj_pt_iszero(in));

	prj_pt_init(out, in->crv);

	fp_init(&XX, out->crv->a.ctx);
	fp_init(&ZZ, out->crv->a.ctx);
	fp_init(&w, out->crv->a.ctx);
	fp_init(&s, out->crv->a.ctx);
	fp_init(&ss, out->crv->a.ctx);
	fp_init(&sss, out->crv->a.ctx);
	fp_init(&R, out->crv->a.ctx);
	fp_init(&RR, out->crv->a.ctx);
	fp_init(&B, out->crv->a.ctx);
	fp_init(&h, out->crv->a.ctx);

	/* XX = X1² */
	fp_sqr_monty(&XX, &(in->X));

	/* ZZ = Z1² */
	fp_sqr_monty(&ZZ, &(in->Z));

	/* w = a*ZZ+3*XX */
	fp_mul_monty(&w, &(in->crv->a_monty), &ZZ);
	fp_add_monty(&w, &w, &XX);
	fp_add_monty(&w, &w, &XX);
	fp_add_monty(&w, &w, &XX);

	/* s = 2*Y1*Z1 */
	fp_mul_monty(&s, &(in->Y), &(in->Z));
	fp_add_monty(&s, &s, &s);

	/* ss = s² */
	fp_sqr_monty(&ss, &s);

	/* sss = s*ss */
	fp_mul_monty(&sss, &s, &ss);

	/* R = Y1*s */
	fp_mul_monty(&R, &(in->Y), &s);

	/* RR = R² */
	fp_sqr_monty(&RR, &R);

	/* B = (X1+R)²-XX-RR */
	fp_add_monty(&R, &R, &(in->X));
	fp_sqr_monty(&B, &R);
	fp_sub_monty(&B, &B, &XX);
	fp_sub_monty(&B, &B, &RR);

	/* h = w²-2*B */
	fp_sqr_monty(&h, &w);
	fp_sub_monty(&h, &h, &B);
	fp_sub_monty(&h, &h, &B);

	/* X3 = h*s */
	fp_mul_monty(&(out->X), &h, &s);

	/* Y3 = w*(B-h)-2*RR */
	fp_sub_monty(&B, &B, &h);
	fp_mul_monty(&(out->Y), &w, &B);
	fp_sub_monty(&(out->Y), &(out->Y), &RR);
	fp_sub_monty(&(out->Y), &(out->Y), &RR);

	/* Z3 = sss */
	fp_copy(&(out->Z), &sss);

	fp_uninit(&XX);
	fp_uninit(&ZZ);
	fp_uninit(&w);
	fp_uninit(&s);
	fp_uninit(&ss);
	fp_uninit(&sss);
	fp_uninit(&R);
	fp_uninit(&RR);
	fp_uninit(&B);
	fp_uninit(&h);
#endif
}

/* Aliased version */
static void _prj_pt_dbl_monty(prj_pt_t out, prj_pt_src_t in)
{
	if (out == in) {
		prj_pt out_cpy;
		prj_pt_init(&out_cpy, out->crv);
		prj_pt_copy(&out_cpy, out);
		__prj_pt_dbl_monty(&out_cpy, in);
		prj_pt_copy(out, &out_cpy);
		prj_pt_uninit(&out_cpy);
	} else {
		__prj_pt_dbl_monty(out, in);
	}
}

/* Public version of the doubling to handle the case where the inputs are
 * zero or opposites
 */
void prj_pt_dbl_monty(prj_pt_t out, prj_pt_src_t in)
{
	prj_pt_check_initialized(in);

#ifdef NO_USE_COMPLETE_FORMULAS
	if (prj_pt_iszero(in)) {
		prj_pt_init(out, in->crv);
		prj_pt_zero(out);
	} else {
		_prj_pt_dbl_monty(out, in);
	}
#else
	_prj_pt_dbl_monty(out, in);
#endif
}



/****** Scalar multiplication algorithms *****/

/* If nothing is specified regarding the scalar multiplication algorithm, we use
 * the Montgomery Ladder
 */
#if !defined(USE_DOUBLE_ADD_ALWAYS) && !defined(USE_MONTY_LADDER)
#define USE_MONTY_LADDER
#endif

#if defined(USE_DOUBLE_ADD_ALWAYS) && defined(USE_MONTY_LADDER)
#error "You can either choose USE_DOUBLE_ADD_ALWAYS or USE_MONTY_LADDER, not both!"
#endif

#ifdef USE_DOUBLE_ADD_ALWAYS
/* Double-and-Add-Always masked using Itoh et al. anti-ADPA
 * (Address-bit DPA) countermeasure.
 * See "A Practical Countermeasure against Address-Bit Differential Power Analysis"
 * by Itoh, Izu and Takenaka for more information.
 *
 * NOTE: this masked variant of the Double-and-Add-Always algorithm is always
 * used as it has a very small impact on performance and is inherently more
 * robust againt DPA.
 *
 * NOTE: the Double-and-Add-Always algorithm inherently depends on the MSB of the
 * scalar. In order to avoid leaking this MSB and fall into HNP (Hidden Number
 * Problem) issues, we use the trick described in https://eprint.iacr.org/2011/232.pdf
 * to have the MSB always set. However, since the scalar m might be less or bigger than
 * the order q of the curve, we distinguish three situations:
 *     - The scalar m is < q (the order), in this case we compute:
 *         -
 *        | m' = m + (2 * q) if [log(k + q)] == [log(q)],
 *        | m' = m + q otherwise.
 *         -
 *     - The scalar m is >= q and < q**2, in this case we compute:
 *         -
 *        | m' = m + (2 * (q**2)) if [log(k + (q**2))] == [log(q**2)],
 *        | m' = m + (q**2) otherwise.
 *         -
 *     - The scalar m is >= (q**2), in this case m == m'
 *
 *   => We only deal with 0 <= m < (q**2) using the countermeasure. When m >= (q**2),
 *      we stick with m' = m, accepting MSB issues (not much can be done in this case
 *      anyways). In the two first cases, Double-and-Add-Always is performed in constant
 *      time wrt the size of the scalar m.
 */
static void _prj_pt_mul_ltr_monty_dbl_add_always(prj_pt_t out, nn_src_t m, prj_pt_src_t in)
{
	/* We use Itoh et al. notations here for T and the random r */
	prj_pt T[3];
	bitcnt_t mlen;
	int mbit, rbit;
	/* Random for masking the Double and Add Always algorithm */
	nn r;
	/* Random for projective coordinates masking */
        fp l;
	/* The new scalar we will use with MSB fixed to 1 (noted m' above).
	 * This helps dealing with constant time.
	 */
	nn m_msb_fixed;
	nn order_square;

	/* Check that the input is on the curve */
	MUST_HAVE(prj_pt_is_on_curve(in) == 1);
	/* Compute m' from m depending on the rule described above */
	/* First compute q**2 */
	nn_sqr(&order_square, &(in->crv->order));
	/* Then compute m' depending on m size */
	if(nn_cmp(m, &(in->crv->order)) < 0){
		/* Case where m < q */
		nn_add(&m_msb_fixed, m, &(in->crv->order));
		bitcnt_t msb_bit_len = nn_bitlen(&m_msb_fixed);
		bitcnt_t order_bitlen = nn_bitlen(&(in->crv->order));
		nn_cnd_add((msb_bit_len == order_bitlen), &m_msb_fixed, &m_msb_fixed, &(in->crv->order));
	}
	else if(nn_cmp(m, &order_square) < 0){
		/* Case where m >= q and m < (q**2) */
		nn_add(&m_msb_fixed, m, &order_square);
		bitcnt_t msb_bit_len = nn_bitlen(&m_msb_fixed);
		bitcnt_t order_square_bitlen = nn_bitlen(&order_square);
		nn_cnd_add((msb_bit_len == order_square_bitlen), &m_msb_fixed, &m_msb_fixed, &order_square);

	}
	else{
		/* Case where m >= (q**2) */
		nn_copy(&m_msb_fixed, m);
	}
	mlen = nn_bitlen(&m_msb_fixed);
	if(mlen == 0){
		/* Should not happen thanks to our MSB fixing trick, but in case ...
		 * Return the infinite point.
		 */
		prj_pt_init(out, in->crv);
		prj_pt_zero(out);
		return;
	}
	mlen--;

	/* Get a random r with the same size of m_msb_fixed */
	MUST_HAVE(!nn_get_random_len(&r, m_msb_fixed.wlen * WORD_BYTES));
        /* Get a random value l in Fp */
	MUST_HAVE(!fp_get_random(&l, in->X.ctx));
	rbit = nn_getbit(&r, mlen);

	/* Initialize points */
	prj_pt_init(&T[0], in->crv);
	prj_pt_init(&T[1], in->crv);
        /* 
	 * T[2] = R(P)
	 * Blind the point with projective coordinates (X, Y, Z) => (l*X, l*Y, l*Z)
         */
	prj_pt_init(&T[2], in->crv);
        fp_mul_monty(&(T[2].X), &(in->X), &l);
        fp_mul_monty(&(T[2].Y), &(in->Y), &l);
        fp_mul_monty(&(T[2].Z), &(in->Z), &l);

	/*  T[r[n-1]] = T[2] */
	prj_pt_copy(&T[rbit], &T[2]);

	/* Main loop of Double and Add Always */
	while (mlen > 0) {
		int rbit_next;
		--mlen;
		/* rbit is r[i+1], and rbit_next is r[i] */
		rbit_next = nn_getbit(&r, mlen);
		/* mbit is m[i] */
		mbit = nn_getbit(&m_msb_fixed, mlen);
		/* Double: T[r[i+1]] = ECDBL(T[r[i+1]]) */
		prj_pt_dbl_monty(&T[rbit], &T[rbit]);
		/* Add:  T[1-r[i+1]] = ECADD(T[r[i+1]],T[2]) */
		prj_pt_add_monty(&T[1-rbit], &T[rbit], &T[2]);
		/* T[r[i]] = T[d[i] ^ r[i+1]] 
		 * NOTE: we use the low level nn_copy function here to avoid
		 * any possible leakage on operands with prj_pt_copy
		 */
		nn_copy(&(T[rbit_next].X.fp_val), &(T[mbit ^ rbit].X.fp_val));
		nn_copy(&(T[rbit_next].Y.fp_val), &(T[mbit ^ rbit].Y.fp_val));
		nn_copy(&(T[rbit_next].Z.fp_val), &(T[mbit ^ rbit].Z.fp_val));
		/* Update rbit */
		rbit = rbit_next;
	}
	/* Output: T[r[0]] */
	prj_pt_copy(out, &T[rbit]);
	/* Check that the output is on the curve */
	MUST_HAVE(prj_pt_is_on_curve(out) == 1);

	prj_pt_uninit(&T[0]);
	prj_pt_uninit(&T[1]);
	prj_pt_uninit(&T[2]);
	nn_uninit(&r);
	fp_uninit(&l);
	nn_uninit(&m_msb_fixed);
	nn_uninit(&order_square);
}
#endif

#ifdef USE_MONTY_LADDER
/* Montgomery Ladder masked using Itoh et al. anti-ADPA
 * (Address-bit DPA) countermeasure.
 * See "A Practical Countermeasure against Address-Bit Differential Power Analysis"
 * by Itoh, Izu and Takenaka for more information.
 *
 * NOTE: this masked variant of the Montgomery Ladder algorithm is always
 * used as it has a very small impact on performance and is inherently more
 * robust againt DPA.
 *
 * NOTE: the Montgomery Ladder algorithm inherently depends on the MSB of the
 * scalar. In order to avoid leaking this MSB and fall into HNP (Hidden Number
 * Problem) issues, we use the trick described in https://eprint.iacr.org/2011/232.pdf
 * to have the MSB always set. However, since the scalar m might be less or bigger than
 * the order q of the curve, we distinguish three situations:
 *     - The scalar m is < q (the order), in this case we compute:
 *         -
 *        | m' = m + (2 * q) if [log(k + q)] == [log(q)],
 *        | m' = m + q otherwise.
 *         -
 *     - The scalar m is >= q and < q**2, in this case we compute:
 *         -
 *        | m' = m + (2 * (q**2)) if [log(k + (q**2))] == [log(q**2)],
 *        | m' = m + (q**2) otherwise.
 *         -
 *     - The scalar m is >= (q**2), in this case m == m'
 *
 *   => We only deal with 0 <= m < (q**2) using the countermeasure. When m >= (q**2),
 *      we stick with m' = m, accepting MSB issues (not much can be done in this case
 *      anyways). In the two first cases, Montgomery Ladder is performed in constant
 *      time wrt the size of the scalar m.
 */
static void _prj_pt_mul_ltr_monty_ladder(prj_pt_t out, nn_src_t m, prj_pt_src_t in)
{
	/* We use Itoh et al. notations here for T and the random r */
	prj_pt T[3];
	bitcnt_t mlen;
	int mbit, rbit;
	/* Random for masking the Montgomery Ladder algorithm */
	nn r;
	/* Random for projective coordinates masking */
        fp l;
	/* The new scalar we will use with MSB fixed to 1 (noted m' above).
	 * This helps dealing with constant time.
	 */
	nn m_msb_fixed;
	nn order_square;

	/* Check that the input is on the curve */
	MUST_HAVE(prj_pt_is_on_curve(in) == 1);

	/* Compute m' from m depending on the rule described above */
	/* First compute q**2 */
	nn_sqr(&order_square, &(in->crv->order));
	/* Then compute m' depending on m size */
	if(nn_cmp(m, &(in->crv->order)) < 0){
		/* Case where m < q */
		nn_add(&m_msb_fixed, m, &(in->crv->order));
		bitcnt_t msb_bit_len = nn_bitlen(&m_msb_fixed);
		bitcnt_t order_bitlen = nn_bitlen(&(in->crv->order));
		nn_cnd_add((msb_bit_len == order_bitlen), &m_msb_fixed, &m_msb_fixed, &(in->crv->order));
	}
	else if(nn_cmp(m, &order_square) < 0){
		/* Case where m >= q and m < (q**2) */
		nn_add(&m_msb_fixed, m, &order_square);
		bitcnt_t msb_bit_len = nn_bitlen(&m_msb_fixed);
		bitcnt_t order_square_bitlen = nn_bitlen(&order_square);
		nn_cnd_add((msb_bit_len == order_square_bitlen), &m_msb_fixed, &m_msb_fixed, &order_square);

	}
	else{
		/* Case where m >= (q**2) */
		nn_copy(&m_msb_fixed, m);
	}
	mlen = nn_bitlen(&m_msb_fixed);
	if(mlen == 0){
		/* Should not happen thanks to our MSB fixing trick, but in case ...
		 * Return the infinite point.
		 */
		prj_pt_init(out, in->crv);
		prj_pt_zero(out);
		return;
	}
	mlen--;

	/* Get a random r with the same size of m_msb_fixed */
	MUST_HAVE(!nn_get_random_len(&r, m_msb_fixed.wlen * WORD_BYTES));
        /* Get a random value l in Fp */
	MUST_HAVE(!fp_get_random(&l, in->X.ctx));
	rbit = nn_getbit(&r, mlen);

	/* Initialize points */
	prj_pt_init(&T[0], in->crv);
	prj_pt_init(&T[1], in->crv);
	prj_pt_init(&T[2], in->crv);

	/* Initialize T[r[n-1]] to input point */
	prj_pt_copy(&T[rbit], in);
        /* Blind the point with projective coordinates (X, Y, Z) => (l*X, l*Y, l*Z)
         */
        fp_mul_monty(&(T[rbit].X), &(T[rbit].X), &l);
        fp_mul_monty(&(T[rbit].Y), &(T[rbit].Y), &l);
        fp_mul_monty(&(T[rbit].Z), &(T[rbit].Z), &l);
	/* Initialize T[1-r[n-1]] with ECDBL(T[r[n-1]])) */
	prj_pt_dbl_monty(&T[1-rbit], &T[rbit]);

	/* Main loop of the Montgomery Ladder */
	while (mlen > 0) {
		int rbit_next;
		--mlen;
		/* rbit is r[i+1], and rbit_next is r[i] */
		rbit_next = nn_getbit(&r, mlen);
		/* mbit is m[i] */
		mbit = nn_getbit(&m_msb_fixed, mlen);
		/* Double: T[2] = ECDBL(T[d[i] ^ r[i+1]]) */
		prj_pt_dbl_monty(&T[2], &T[mbit ^ rbit]);
		/* Add: T[1] = ECADD(T[0],T[1]) */
		prj_pt_add_monty(&T[1], &T[0], &T[1]);
		/* T[0] = T[2-(d[i] ^ r[i])] */
		/* NOTE: we use the low level nn_copy function here to avoid
		 * any possible leakage on operands with prj_pt_copy
		 */
		nn_copy(&(T[0].X.fp_val), &(T[2-(mbit ^ rbit_next)].X.fp_val));
		nn_copy(&(T[0].Y.fp_val), &(T[2-(mbit ^ rbit_next)].Y.fp_val));
		nn_copy(&(T[0].Z.fp_val), &(T[2-(mbit ^ rbit_next)].Z.fp_val));
		/* T[1] = T[1+(d[i] ^ r[i])] */
		/* NOTE: we use the low level nn_copy function here to avoid
		 * any possible leakage on operands with prj_pt_copy
		 */
		nn_copy(&(T[1].X.fp_val), &(T[1+(mbit ^ rbit_next)].X.fp_val));
		nn_copy(&(T[1].Y.fp_val), &(T[1+(mbit ^ rbit_next)].Y.fp_val));
		nn_copy(&(T[1].Z.fp_val), &(T[1+(mbit ^ rbit_next)].Z.fp_val));
		/* Update rbit */
		rbit = rbit_next;
	}
	/* Output: T[r[0]] */
	prj_pt_copy(out, &T[rbit]);
	/* Check that the output is on the curve */
	MUST_HAVE(prj_pt_is_on_curve(out) == 1);

	prj_pt_uninit(&T[0]);
	prj_pt_uninit(&T[1]);
	prj_pt_uninit(&T[2]);
	nn_uninit(&r);
	fp_uninit(&l);
	nn_uninit(&m_msb_fixed);
	nn_uninit(&order_square);
}
#endif

/* Main projective scalar multiplication function.
 * Depending on the preprocessing options, we use either the
 * Double and Add Always algorithm, or the Montgomery Ladder one.
 */
static void _prj_pt_mul_ltr_monty(prj_pt_t out, nn_src_t m, prj_pt_src_t in){
#if defined(USE_DOUBLE_ADD_ALWAYS)
	_prj_pt_mul_ltr_monty_dbl_add_always(out, m, in);
#elif defined(USE_MONTY_LADDER)
	_prj_pt_mul_ltr_monty_ladder(out, m, in);
#else
#error "Error: neither Double and Add Always nor Montgomery Ladder has been selected!"
#endif
	return;
}


/* Aliased version */
void prj_pt_mul_ltr_monty(prj_pt_t out, nn_src_t m, prj_pt_src_t in)
{
	prj_pt_check_initialized(in);
	nn_check_initialized(m);

	if (out == in) {
		prj_pt out_cpy;
		prj_pt_init(&out_cpy, out->crv);
		prj_pt_copy(&out_cpy, out);
		_prj_pt_mul_ltr_monty(&out_cpy, m, in);
		prj_pt_copy(out, &out_cpy);
		prj_pt_uninit(&out_cpy);
	} else {
		_prj_pt_mul_ltr_monty(out, m, in);
	}
}



void prj_pt_mul_monty(prj_pt_t out, nn_src_t m, prj_pt_src_t in)
{
	prj_pt_mul_ltr_monty(out, m, in);
}

int prj_pt_mul_monty_blind(prj_pt_t out, nn_src_t m, prj_pt_src_t in, nn_t b, nn_src_t q)
{
	/* Blind the scalar m with (b*q) */
	nn_mul(b, b, q);
	nn_add(b, b, m);
	/* NOTE: point blinding is performed in the lower
	 * functions
	 */

        /* Perform the scalar multiplication */
	prj_pt_mul_ltr_monty(out, b, in);

	/* Zero the mask to avoid information leak */
	nn_zero(b);
	return 0;
}

static void _jprj_pt_dbl_monty(prj_pt_t out, prj_pt_src_t in){

	// ext_printf("_jprj_pt_dbl_monty\n");

	prj_pt_init(out, in->crv);
	if(prj_pt_iszero(in)){
		prj_pt_zero(out);
		return;
	}

	fp x2, x4, y2, y4, z2;
	fp_init(&x2, out->crv->a.ctx);
	fp_init(&x4, out->crv->a.ctx);
	fp_init(&y2, out->crv->a.ctx);
	fp_init(&y4, out->crv->a.ctx);
	fp_init(&z2, out->crv->a.ctx);

	/* x2 = 3x^2 */

	fp_mul_monty(&z2, &in->Z, &in->Z);

	// fp_mul_monty(&z2, &z2, &z2);
	// fp_mul_monty(&z2, &z2, &out->crv->a_monty);
	// fp_mul_monty(&x2, &in->X, &in->X);
	// fp_add_monty(&x4, &x2, &x2);
	// fp_add_monty(&x2, &x4, &x2);
	// fp_add_monty(&x2, &x2, &z2);

	/* M = 3*(X1-Z12)*(X1+Z12) */
	fp_add_monty(&x2, &in->X, &z2);
	fp_sub_monty(&x4, &in->X, &z2);
	fp_mul_monty(&x2, &x2, &x4);
	fp_add_monty(&x4, &x2, &x2);
	fp_add_monty(&x2, &x4, &x2);



	/* M^2 */
	fp_mul_monty(&x4, &x2, &x2);

	// 2y^2
	fp_mul_monty(&y2, &in->Y, &in->Y);
	fp_add_monty(&y2, &y2, &y2);

	// y4 = 8y^4
	fp_mul_monty(&y4, &y2, &y2);
	fp_add_monty(&y4, &y4, &y4);

	// y2 = 4y^2
	fp_add_monty(&y2, &y2, &y2);
	
	/* S = 4xy^2   */
	fp_mul_monty(&y2, &y2, &in->X);

	/* X = T = M^2 - 2*s */
	fp_sub_monty(&out->X, &x4, &y2);
	fp_sub_monty(&out->X, &out->X, &y2);

	/* Y3 = M*(S-T)-8*y^4 */
	fp_sub_monty(&out->Y, &y2, &out->X);
	fp_mul_monty(&out->Y, &out->Y, &x2);
	fp_sub_monty(&out->Y, &out->Y, &y4);

	fp_mul_monty(&out->Z, &in->Z, &in->Y);
	fp_add_monty(&out->Z, &out->Z, &out->Z);

	fp_uninit(&x2);
	fp_uninit(&x4);
	fp_uninit(&y2);
	fp_uninit(&y4);
	fp_uninit(&z2);
}

static void jprj_pt_dbl_monty(prj_pt_t out, prj_pt_src_t in){
	if (out == in) {
		prj_pt out_cpy;
		prj_pt_init(&out_cpy, out->crv);
		prj_pt_copy(&out_cpy, out);
		_jprj_pt_dbl_monty(&out_cpy, in);
		prj_pt_copy(out, &out_cpy);
		prj_pt_uninit(&out_cpy);
	} else {
		_jprj_pt_dbl_monty(out, in);
	}
}


static void _jprj_pt_add_monty(prj_pt_t out, prj_pt_src_t in1, prj_pt_src_t in2){

	// ext_printf("_jprj_pt_add_monty\n");

	// ext_printf("enter in jprj_pt_add_monty");

	MUST_HAVE(in1->crv == in2->crv);
	prj_pt_init(out, in1->crv);
	if(prj_pt_iszero(in1)){
		prj_pt_copy(out, in2);
		return;
	}

	if(prj_pt_iszero(in2)){
		prj_pt_copy(out, in1);
		return;
	}


	fp u1, u2, s1, s2, tz1, tz2, h, r, r2, h2, h3;

	fp_init(&u1, out->crv->a.ctx);
	fp_init(&u2, out->crv->a.ctx);
	fp_init(&s1, out->crv->a.ctx);
	fp_init(&s2, out->crv->a.ctx);
	fp_init(&tz1, out->crv->a.ctx);
	fp_init(&tz2, out->crv->a.ctx);
	fp_init(&h, out->crv->a.ctx);
	fp_init(&r, out->crv->a.ctx);
	fp_init(&r2, out->crv->a.ctx);
	fp_init(&h2, out->crv->a.ctx);
	fp_init(&h3, out->crv->a.ctx);

	fp_mul_monty(&tz1, &in1->Z, &in1->Z);
	fp_mul_monty(&tz2, &in2->Z, &in2->Z);

	fp_mul_monty(&u1, &in1->X, &tz2);
	fp_mul_monty(&u2, &in2->X, &tz1);

	fp_mul_monty(&tz1, &tz1, &in1->Z);
	fp_mul_monty(&tz2, &tz2, &in2->Z);

	fp_mul_monty(&s1, &in1->Y, &tz2);
	fp_mul_monty(&s2, &in2->Y, &tz1);

	fp_sub_monty(&h, &u2, &u1);
	fp_sub_monty(&r, &s2, &s1);

	if(fp_iszero(&h) && fp_iszero(&r)){

		// ext_printf("_jprj_pt_add_monty zero\n");
		jprj_pt_dbl_monty(out, in1);
	}else{
		fp_mul_monty(&r2, &r, &r);
		fp_mul_monty(&h2, &h, &h);
		fp_mul_monty(&h3, &h2, &h);

		fp_mul_monty(&u1, &u1, &h2);

		fp_sub_monty(&out->X, &r2, &h3);
		fp_sub_monty(&out->X, &out->X, &u1);
		fp_sub_monty(&out->X, &out->X, &u1);

		fp_mul_monty(&s1, &s1, &h3);

		fp_sub_monty(&out->Y, &u1, &out->X);
		fp_mul_monty(&out->Y, &out->Y, &r);
		fp_sub_monty(&out->Y, &out->Y, &s1);

		fp_mul_monty(&out->Z, &in1->Z, &in2->Z);
		fp_mul_monty(&out->Z, &out->Z, &h);
	}

	fp_uninit(&u1);
	fp_uninit(&u2);
	fp_uninit(&s1);
	fp_uninit(&s2);
	fp_uninit(&tz1);
	fp_uninit(&tz2);
	fp_uninit(&h);
	fp_uninit(&r);
	fp_uninit(&r2);
	fp_uninit(&h2);
	fp_uninit(&h3);
	// ext_printf("_jprj_pt_add_monty end\n");
}


static void jprj_pt_add_monty(prj_pt_t out, prj_pt_src_t in1, prj_pt_src_t in2){
	if ((out == in1) || (out == in2)) {
		prj_pt out_cpy;
		prj_pt_init(&out_cpy, out->crv);
		prj_pt_copy(&out_cpy, out);
		_jprj_pt_add_monty(&out_cpy, in1, in2);
		prj_pt_copy(out, &out_cpy);
		prj_pt_uninit(&out_cpy);
	} else {
		_jprj_pt_add_monty(out, in1, in2);
	}
}

/*
precomp points = [1, 3, 5, 2n + 1,....2^(w-1)] multiply point in
*/
void get_pre_comp_points(prj_pt_t pre_comp, prj_pt_src_t in, int size){

	prj_pt in2;

	prj_pt_copy(&pre_comp[0], in);
	jprj_pt_dbl_monty(&in2, in);

	int n = 1;
	while (n < size){
		jprj_pt_add_monty(&pre_comp[n], &pre_comp[n - 1], &in2);
		n++;
	}

	prj_pt_uninit(&in2);
}

int ecmult_wnaf(int * wnag, nn_src_t m, int window){

	nn temp, temp2, w2exp, w2exp1;
	nn_init(&temp, 4);
	nn_init(&temp2, 4);
	nn_init(&w2exp, 4);
	nn_init(&w2exp1, 4);

	nn_set_word_value(&w2exp, 1 << window);
	nn_set_word_value(&w2exp1, 1 << (window - 1));

	nn_copy(&temp, m);
	int n = 0;

	while(nn_cmp_word(&temp, 0) > 0){
		if (nn_isodd(&temp)){

			nn_mod(&temp2, &temp, &w2exp);
			if(nn_cmp(&temp2, &w2exp1) > 0){
				*(wnag + n) = temp2.val[0] - (1 << window);

				nn_add(&temp, &temp, &w2exp);
				nn_sub(&temp, &temp, &temp2);
			} else {
				*(wnag + n) = temp2.val[0];
				nn_sub(&temp, &temp, &temp2);
			}

		}else{
			*(wnag + n) = 0;
		}
		nn_rshift(&temp, &temp, 1);
		n++;
	}
	nn_uninit(&temp);
	nn_uninit(&temp2);
	nn_uninit(&w2exp);
	nn_uninit(&w2exp1);

	return n;
}


void prj_pt_ec_mult_wnaf(prj_pt_t out, nn_src_t m, prj_pt_src_t in11, nn_src_t n, prj_pt_src_t in3)
{
	prj_pt out2, p1, p2;
	prj_pt_init(&p1, in3->crv);
	prj_pt_init(&p2, in3->crv);
	prj_pt_mul_monty(&p1, m, in11);
	prj_pt_mul_monty(&p2, n, in3);
	prj_pt_add_monty(&out2, &p1, &p2);
	#ifdef VERBOSE_INNER_VALUES
	#undef EC_SIG_ALG
	#define EC_SIG_ALG "WNAF"
	#endif
	dbg_nn_print("m", m);
	dbg_ec_point_print("in1", in11);
	dbg_nn_print("n", n);
	dbg_ec_point_print("in2", in3);
	dbg_ec_point_print("out = m*in1 + n*in2", &out2);

	prj_pt in22, in111;
	prj_pt_t in2, in1;

	in2 = &in22;
	in1 = &in111;
	prj_pt_init(in2, in3->crv);
	prj_pt_init(in1, in3->crv);

	prj_pt_copy(in1, in11);
	prj_pt_copy(in2, in3);
	// TOOD: For some reasons yet to be investigated, below algorithm
	// works only for projective points whose z coordinate is 1.
	prj_pt_normalize(in1);
	prj_pt_normalize(in2);

	// fp inv;
	// fp_init(&inv, in3->crv->a.ctx);
	// fp_inv(&inv, &in3->Z);

	// fp_mul(&(in2)->X, &in3->X, &inv);
	// fp_mul(&(in2)->Y, &in3->Y, &inv);
	// fp_one(&(in2)->Z);

	// fp_uninit(&inv);

	fp_redcify(&in1->X, &in1->X);
	fp_redcify(&in1->Y, &in1->Y);
	fp_redcify(&in1->Z, &in1->Z);

	fp_redcify(&in2->X, &in2->X);
	fp_redcify(&in2->Y, &in2->Y);
	fp_redcify(&in2->Z, &in2->Z);

	// dbg_ec_point_print("in1", in1);
	// dbg_nn_print("in1 X", &in1->X.fp_val);
	// dbg_nn_print("in1 Y", &in1->Y.fp_val);
	// dbg_nn_print("in1 Z", &in1->Z.fp_val);

	// dbg_nn_print("in2 X", &in2->X.fp_val);
	// dbg_nn_print("in2 Y", &in2->Y.fp_val);
	// dbg_nn_print("in2 Z", &in2->Z.fp_val);

	// calculate precomputation for in1 and in2
	int window = 5;
	int pre_comp_size = 1 << (window - 2);

	// ext_printf("window size %d\n", window);
	// ext_printf("pre_comp_size %d\n", pre_comp_size);

	prj_pt neg_pt;
	prj_pt pre_comp_m[pre_comp_size];
	prj_pt pre_comp_n[pre_comp_size];

	nn mr, nr;

	// prj_pt_init(&neg_pt, in2->crv);
	int m_wnag[512], n_wnag[512];

	get_pre_comp_points(pre_comp_m, in1, pre_comp_size);
	get_pre_comp_points(pre_comp_n, in2, pre_comp_size);


	nn_mod(&mr, m, &(in1->crv->order));
	nn_mod(&nr, n, &(in2->crv->order));


	bitcnt_t m_bit_len = ecmult_wnaf(m_wnag, &mr, window);
	bitcnt_t n_bit_len = ecmult_wnaf(n_wnag, &nr, window);
	// bitcnt_t m_bit_len = nn_bitlen(m);
	// bitcnt_t n_bit_len = nn_bitlen(n);

	bitcnt_t bit_len = m_bit_len > n_bit_len ? m_bit_len : n_bit_len;

	// ext_printf("bit_len = %d\n", bit_len);



	prj_pt_init(&neg_pt, in1->crv);
	prj_pt_init(out, in1->crv);
	// out->X = in2->X;
	// prj_pt_init(out, in2->crv);
	prj_pt_zero(out);
	// prj_pt_copy(out, in1);

	// dbg_ec_point_print("out", out);

	int i;

	int no;
	for (i = bit_len - 1; i >= 0; i--)
	{
		// ext_printf("loop %d\n", i);
		jprj_pt_dbl_monty(out, out);
		// if(!prj_pt_iszero(out)){
		// 	dbg_ec_point_print("out", out);
		// }

		if (i < m_bit_len)
		{
			no = m_wnag[i];
			// ext_printf("m_wnag[i] = %d \n", no);
			if (no > 0)
			{
				jprj_pt_add_monty(out, out, &pre_comp_m[(no-1)/2]);
			}
			else if (no < 0)
			{
				//get negative pre_comp_m, then add
				prj_pt_copy(&neg_pt, &pre_comp_m[(-no-1)/2]);
				fp_neg(&(neg_pt.Y), &(neg_pt.Y));

				jprj_pt_add_monty(out, out, &neg_pt);
			}
		}

		if (i < n_bit_len)
		{
			no = n_wnag[i];
			// ext_printf("n_wnag[i] = %d \n", no);
			if (no > 0)
			{
				jprj_pt_add_monty(out, out, &pre_comp_n[(no-1)/2]);
			}
			else if (no < 0)
			{
				//get negative pre_comp_m, then add
				prj_pt_copy(&neg_pt, &pre_comp_n[(-no-1)/2]);
				fp_neg(&(neg_pt.Y), &(neg_pt.Y));

				jprj_pt_add_monty(out, out, &neg_pt);
			}
		}

	}

	fp_unredcify(&out->X, &out->X);
	fp_unredcify(&out->Y, &out->Y);
	fp_unredcify(&out->Z, &out->Z);

	fp zinv2, zinv3;
	fp_init(&zinv2, out->crv->a.ctx);
	fp_init(&zinv3, out->crv->a.ctx);

	fp_inv(&zinv3, &out->Z);
	fp_mul(&zinv2, &zinv3, &zinv3);
	fp_mul(&zinv3, &zinv3, &zinv2);
	fp_mul(&out->X, &out->X, &zinv2);
	fp_mul(&out->Y, &out->Y, &zinv3);
	fp_one(&out->Z);

	dbg_ec_point_print("wNAF out = m*in1 + n*in2", out);
	MUST_HAVE(prj_pt_cmp(out, &out2) == 0);
	fp_uninit(&zinv2);
	fp_uninit(&zinv3);

	nn_uninit(&mr);
	nn_uninit(&nr);
	prj_pt_uninit(&neg_pt);
	for (i = 0; i < pre_comp_size; i++)
	{
		prj_pt_uninit(&pre_comp_m[i]);
		prj_pt_uninit(&pre_comp_n[i]);
	}

	prj_pt_uninit(in1);
	prj_pt_uninit(in2);
}
