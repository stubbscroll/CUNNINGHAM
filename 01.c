/* extremely naive implementation of a program that finds cunningham
   chains of all kinds such that the base prime is B-1 or B+1 where B is a
   multiple of a sha256 hash. after trying the first 1 million multiples of
   the hash, another hash is generated. also, crude stats
   nb, requires external library gmp */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>
#include <gmp.h>
#include "sha256.h"

#define TRY 1000000

typedef long long ll;

double gettime() {
  struct timeval t;
  gettimeofday(&t,NULL);
  return t.tv_sec+t.tv_usec/1000000.;
}

char hex(char c) {
	if(c>9) return c-10+'a';
	else return c+48;
}

ll num[50][3]; /* stats */

mpz_t two;
mpz_t res;
mpz_t power;
mpz_t temp;

/* fermat test with base 2, return 0 if composite */
int fermattest(mpz_t p) {
	mpz_powm(res,two,p,p);
	/* 2^p mod p != 2 means p is certainly composite */
	return 0==mpz_cmp(two,res);
}

/* euler-lagrange-lifchitz probable primality test
   http://www.primenumbers.net/Henri/us/NouvTh1us.htm */
/* check if 2^p = eq (mod 2p+rel) */
int eulerlagrangelifchitz(mpz_t p,int eq,int rel) {
	return 1;
	mpz_add(power,p,p);
	mpz_add_ui(power,power,rel);
	mpz_powm(res,two,p,power);
	if(eq==1) return 0==mpz_cmp_si(res,1);
	else {
		/* res equal to power-1 */
		mpz_sub_ui(temp,power,1);
		return 0==mpz_cmp(temp,res);
	}
}

/* chain of type 1: p=2p+1 */
int findchain1stupid(mpz_t in,double *f) {
	int len=0;
	double z;
	mpz_t p;
	if(!mpz_tstbit(in,0)) { *f=0; return 0; }
	mpz_init_set(p,in);
	while(fermattest(p) && len<48) {
		len++;
		if(mpz_tstbit(p,1)) {
			/* p=3 (mod 4): check 2^p = 1 (mod 2p+1) */
			if(!eulerlagrangelifchitz(p,1,1)) goto fail;
		} else {
			/* p=1 (mod 4): check 2^p = -1 (mod 2p+1) */
			if(!eulerlagrangelifchitz(p,-1,1)) goto fail;
		}
		mpz_add(p,p,p);
		mpz_add_ui(p,p,1);
	}
	/* from p (which is composite) calculate fractional chain length */
	z=mpz_get_d(p);
	*f=(z-mpz_get_d(res))/z;
	mpz_clear(p);
	return len;
fail:
	/* calculate fractional chain length based on failing euler-lagrange-lifchitz */
	z=mpz_get_d(power);
	*f=(z-mpz_get_d(res))/z;
	mpz_clear(p);
	return len;
}

/* chain of type 2: p=2p-1 */
int findchain2stupid(mpz_t in,double *f) {
	int len=0;
	double z;
	mpz_t p;
	if(!mpz_tstbit(in,0)) { *f=0; return 0; }
	mpz_init_set(p,in);
	while(fermattest(p) && len<48) {
		len++;
		if(mpz_tstbit(p,1)) {
			/* p=3 (mod 4): check 2^p = -1 (mod 2p-1) */
			if(!eulerlagrangelifchitz(p,-1,-1)) goto fail;
		} else {
			/* p=1 (mod 4): check 2^p = 1 (mod 2p-1) */
			if(!eulerlagrangelifchitz(p,1,-1)) goto fail;
		}
		mpz_add(p,p,p);
		mpz_sub_ui(p,p,1);
	}
	/* from p (which is composite) calculate fractional chain length */
	z=mpz_get_d(p);
	*f=(z-mpz_get_d(res))/z;
	mpz_clear(p);
	return len;
fail:
	/* calculate fractional chain length based on failing euler-lagrange-lifchitz */
	z=mpz_get_d(power);
	*f=(z-mpz_get_d(res))/z;
	mpz_clear(p);
	return len;
}

void work() {
	int i,l1,l2,l3;
	unsigned char s[10],p[32];
	char t[65];
	double start=gettime(),f1,f2,tid;
	mpz_t base,origin;
	mpz_init(base);
	mpz_init(origin);
	memset(num,0,sizeof(num));
	while(1) {
		/* take sha-256 of a random string of 10 chars */
		for(i=0;i<10;i++) s[i]=rand()&255;
		sha256(s,10,p);
		for(i=0;i<32;i++) t[i*2]=hex(p[i]>>4),t[i*2+1]=hex(p[i]&15);
		t[64]=0;
		printf("try hash %s\n",t);
		mpz_set_str(base,t,16);
		for(i=1;i<=TRY;i++) {
			mpz_mul_si(origin,base,i);
			/* given origin:
			   find type 1 chain starting at origin-1 (next in chain: 2p+1)
			   find type 2 chain starting at origin+1 (next in chain: 2p-1)
			   also, bi-twin chain (only even lengths, min of the two types) */
			mpz_sub_ui(origin,origin,1u);
			l1=findchain1stupid(origin,&f1);
			mpz_add_ui(origin,origin,2u);
			l2=findchain2stupid(origin,&f2);
			if(l1>l2) l3=l2+l2;
			else if(l1<l2) l3=l1+l1;
			else l3=l1+l2;
			if(l1) num[l1][0]++;
			if(l2) num[l2][1]++;
			if(l3) num[l3][2]++;
			if(l1>2) printf("found chain type 1 length %.12f\n",l1+f1);
			if(l2>2) printf("found chain type 2 length %.12f\n",l2+f2);
			/* don't know about fractional length here, just take average
			   (which is wrong, since it changes the distribution) */
			if(l3>2) printf("found chain type 3 length %.12f\n",l3+(f1+f2)*.5);
		}
		tid=gettime();
		puts("===============================================================================");
		for(i=3;i<50;i++) if(num[i][0]+num[i][1]+num[i][2]) {
			printf(" %2dch/h: %6.2f [%I64d %I64d %I64d]\n",i,
				(num[i][0]+num[i][1]+num[i][2])/((tid-start)/3600),num[i][0],num[i][1],num[i][2]);
		}
		puts("===============================================================================");
	}
	mpz_clear(origin);
	mpz_clear(base);
}

/* test specific number */
void test(char *s) {
	mpz_t p;
	int len;
	double f;
	mpz_init_set_str(p,s,10);
	len=findchain1stupid(p,&f);
	printf("try %s:\n",s);
	printf("  found %.12f\n",len+f);
	len=findchain2stupid(p,&f);
	printf("  found %.12f\n",len+f);
	mpz_clear(p);
}

/* test routines against known chains */
void sanity() {
	test("978230124172507899911260068253742404889");
	test("335898524600734221050749906451371");
	test("28320350134887132315879689643841");
	test("2368823992523350998418445521");
	test("1302312696655394336638441");
}

int main() {
	mpz_init_set_si(two,2);
	mpz_init(res);
	mpz_init(power);
	mpz_init(temp);
	sanity();
	work();
	mpz_clear(temp);
	mpz_clear(power);
	mpz_clear(res);
	mpz_clear(two);
	return 0;
}
