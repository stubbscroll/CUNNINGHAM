/* multiply hash with primorial.
   this increases the number of candidates greatly, causing the chain check
   phase to take much longer. however, this also increases the number of
   chains found per time spent.
   this version only looks for chains of length 4 or more. it only finds
   3-chains as a result of failing primality tests for 4-chains, hence it will
   find less 3-chains than the previous version.

   tunable parameters:
   SIEVESIZE - smaller means we check smaller numbers in average, but the
     overhead increases. larger means we get to check more long chain
     candidates
   MAXPRIME - larger means more composite numbers are marked in the sieve,
     leading to fewer chain candidates for which to perform expensive primality
     testing on. for each prime, there is a fixed cost (bignum modulo and
     calculation of modular inverse with ints) and a variable cost (sweep over
     sieve array and mark all multiples of prime) which costs less for larger
     primes.
   PRIMORIAL - size of largest prime to multiply in. higher number results in
     more chain candidates (more prime numbers in sieve), but it causes the
     numbers to be tested to be larger. increaing the primorial past a certain
     limit gives diminishing returns - the increase in the number of candidates
     goes down, while the origin increases faster.

   naturally, each version must be tuned from scratch. SIEVESIZE is very
   dependent on the desired chain length, and probably also dependent on
   architecture.
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>
#include <gmp.h>
#include "sha256.h"

#define SIEVESIZE 1000000 /* size of each sieve (in number of elements) */
#define MAXPRIME 150000    /* max prime to check in sieve phase */
#define PRIMORIAL 31

#define MINCHAIN 4                /* minimum length chain to look for */
#define MINTWIN ((MINCHAIN+1)>>1) /* minimum bi-twin chain to look for */

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

int prim[MAXPRIME];
int pn;

int isprime(int n) {
	int i;
	if(n<4) return n>1;
	for(i=2;i*i<=n;i++) if(n%i==0) return 0;
	return 1;
}

void genprimes() {
	int i;
	pn=0;
	prim[pn++]=2;
	for(i=3;i<MAXPRIME;i+=2) if(isprime(i)) prim[pn++]=i;
}

/* find the multiplicative inverse of a modulo p prime */
/* lots of division and modulo here, speed up later by using tricks from
   binary gcd. also duplicate inner loop to avoid swapping */
int inverse(int a,int p) {
	int b=p,x=0,y=1,t,q,lastx=1,lasty=0;
	while(b) {
		q=a/b;
		t=a,a=b,b=t%b;
		t=x,x=lastx-q*x,lastx=t;
		t=y,y=lasty-q*y,lasty=t;
	}
	lastx%=p;
	if(lastx<0) return lastx+p;
	return lastx;
}

ll num[50][3]; /* stats */

char sieveminus[SIEVESIZE]; /* element i is 1 if i*B-1 is composite */
char sieveplus [SIEVESIZE]; /* element i is 1 if i*B+1 is composite */
/* index 0 not in use, as it corresponds to a multiple of 0 */

mpz_t two;
mpz_t res;
mpz_t power;
mpz_t temp,temp2;

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
int findchain1(int mul,mpz_t in,double *f) {
	int len=0;
	double z;
	mpz_mul_si(temp2,in,mul);
	mpz_sub_ui(temp2,temp2,1);
	while(1) {
		if(mul<SIEVESIZE && sieveminus[mul]) break;
		if(!fermattest(temp2)) break;
		len++;
		if(mpz_tstbit(temp2,1)) {
			/* p=3 (mod 4): check 2^p = 1 (mod 2p+1) */
			if(!eulerlagrangelifchitz(temp2,1,1)) goto fail;
		} else {
			/* p=1 (mod 4): check 2^p = -1 (mod 2p+1) */
			if(!eulerlagrangelifchitz(temp2,-1,1)) goto fail;
		}
		mpz_add(temp2,temp2,temp2);
		mpz_add_ui(temp2,temp2,1);
	}
	z=mpz_get_d(temp2);
	*f=(z-mpz_get_d(res))/z;
	return len;
fail:
	/* calculate fractional chain length based on failing euler-lagrange-lifchitz */
	z=mpz_get_d(power);
	*f=(z-mpz_get_d(res))/z;
	return len;
}

/* chain of type 2: p=2p-1 */
int findchain2(int mul,mpz_t in,double *f) {
	int len=0;
	double z;
	mpz_mul_si(temp2,in,mul);
	mpz_add_ui(temp2,temp2,1);
	while(1) {
		if(mul<SIEVESIZE && sieveplus[mul]) break;
		if(!fermattest(temp2)) break;
		len++;
		if(mpz_tstbit(temp2,1)) {
			/* p=3 (mod 4): check 2^p = -1 (mod 2p-1) */
			if(!eulerlagrangelifchitz(temp2,-1,-1)) goto fail;
		} else {
			/* p=1 (mod 4): check 2^p = 1 (mod 2p-1) */
			if(!eulerlagrangelifchitz(temp2,1,-1)) goto fail;
		}
		mpz_add(temp2,temp2,temp2);
		mpz_sub_ui(temp2,temp2,1);
	}
	/* from p (which is composite) calculate fractional chain length */
	z=mpz_get_d(temp2);
	*f=(z-mpz_get_d(res))/z;
	return len;
fail:
	/* calculate fractional chain length based on failing euler-lagrange-lifchitz */
	z=mpz_get_d(power);
	*f=(z-mpz_get_d(res))/z;
	return len;
}

void work() {
	ll tried=0;
	int i,p,a,j,p2,l1,l2,l3;
	double start=gettime(),tid,f1,f2;
	unsigned char s[20],u[32];
	char t[65];
	mpz_t origin,om;
	mpz_init(origin);
	mpz_init(om);
	genprimes();
	memset(num,0,sizeof(num));
	strcpy((char *)s,"sopp");
	while(1) {
		/* take sha-256 of a string with counter appended */
		for(i=0;i<8;i++) s[i+4]=(tried>>(i*8))&255;
		sha256(s,12,u);
		for(i=0;i<32;i++) t[i*2]=hex(u[i]>>4),t[i*2+1]=hex(u[i]&15);
		t[64]=0;
		tried++;
		mpz_set_str(origin,t,16);
		/* multiply primorial */
		for(i=0;prim[i]<=PRIMORIAL;i++)
			if(mpz_fdiv_ui(origin,prim[i])) mpz_mul_ui(origin,origin,prim[i]);
		/* init sieve, all elements start as "probably prime" */
		memset(sieveminus,0,SIEVESIZE);
		memset(sieveplus,0,SIEVESIZE);
		mpz_sub_ui(om,origin,1);
		/* mark multiples of small primes */
		for(i=0;prim[i]<=PRIMORIAL;i++);
		for(;i<pn;i++) if((j=(int)mpz_fdiv_ui(origin,p=prim[i]))) {
			/* find lowest k>=1 such that k*origin-1 = 0 (mod p) which is equivalent
			   to the inverse of origin mod p */
			a=j=inverse(j,p);
			/* mark all multiples in sieve as composite */
			while(j<SIEVESIZE) sieveminus[j]=1,j+=p;
			/* find lowest k>=1 such that k*origin+1 = 0 (mod p) which is equivalent
			   to the inverse of origin mod p. multiply k from previous case by p-1
			*/
			j=(ll)a*(p-1)%p;
			/* mark all multiples in sieve as composite */
			while(j<SIEVESIZE) sieveplus[j]=1,j+=p;
		}
		/* find potential chains in sieve, primality test all numbers in chain
		   - only use as origins odd multiples of hash, or even multiples where
		     half of the multiple is composite in the sieve
		*/
		p2=1;
		for(i=0;i<MINCHAIN;i++) p2*=2;
		/* look for chains */
		for(i=1;i<SIEVESIZE/p2;i++) {
			l1=l2=f1=f2=0;
			/* don't bother to check unless chain is guaranteed to be of length 3
			   (warning, if is hardcoded to 4 - doesn't use macro */
			if(((i&1) || sieveminus[i>>1]) && !sieveminus[i] && !sieveminus[i<<1] && !sieveminus[i<<2] && !sieveminus[i<<3])
				l1=findchain1(i,origin,&f1);
			if(((i&1) || sieveplus[i>>1]) && !sieveplus[i] && !sieveplus[i<<1] && !sieveplus[i<<2] && !sieveplus[i<<3])
				l2=findchain2(i,origin,&f2);
			if(l1>l2) l3=l2+l2;
			else if(l1<l2) l3=l1+l1;
			else l3=l1+l2;
			if(l1) num[l1][0]++;
			if(l2) num[l2][1]++;
			if(l3) num[l3][2]++;
			if(l1>4) printf("found chain type 1 length %.12f\n",l1+f1);
			if(l2>4) printf("found chain type 2 length %.12f\n",l2+f2);
			/* don't know about fractional length here, just take average
			   (which is wrong, since it changes the distribution) */
			if(l3>4) printf("found chain type 3 length %.12f\n",l3+(f1+f2)*.5);
		}
		if(tried%50==0) {
			tid=gettime();
			puts("===============================================================================");
			printf("after trying %I64d hashes:\n",tried);
			for(i=3;i<50;i++) if(num[i][0]+num[i][1]+num[i][2]) {
				printf(" %2dch/h: %9.2f [%I64d %I64d %I64d]\n",i,
					(num[i][0]+num[i][1]+num[i][2])/((tid-start)/3600),num[i][0],num[i][1],num[i][2]);
			}
			puts("===============================================================================");
		}
	}
}

int main() {
	mpz_init_set_si(two,2);
	mpz_init(res);
	mpz_init(power);
	mpz_init(temp);
	mpz_init(temp2);
	work();
	return 0;
}
