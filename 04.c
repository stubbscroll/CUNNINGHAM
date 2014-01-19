/* smarter order of doing primality check: divide and conquer
   given a potential chain of length n, do primality check of middle
   number. if it fails, split into two separate chains, or throw away if
   resulting chain is too short (5 is the least interesting length).
   doesn't really look for bichains.

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
   MINACCEPT - minimum length chain to accept, want this to be as high as
     possible (to abort early and save us from doing primality tests)
   MINCHAIN - minimum length chain (from sieve) to run primality tests on, we
     also want this to be as high as possible (to avoid spending time doing
     primality tests on short chains)
   BEYOND - extend chains beyond sieve at the cost of doing more primality tests
     (full primality testing beyond sieve), but at the benefit of hopefully
     finding more chains)

   naturally, each version must be tuned from scratch. SIEVESIZE is very
   dependent on the desired chain length, and probably also dependent on
   architecture.
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <sys/time.h>
#include <gmp.h>
#include "sha256.h"

#define SIEVESIZE 1000000 /* size of each sieve (in number of elements) */
#define MAXPRIME 50000   /* max prime to check in sieve phase */
#define PRIMORIAL 31

#define BEYOND            /* define if we want to extend chains beyond sieve */

/* define if we want to sanity-check fast algorithm */
/*#define SANITY*/

#define MINACCEPT 5               /* minimum length chain to accept */
#define MINCHAIN 6                /* minimum length chain to look for */
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

mpz_t two;
mpz_t res;
mpz_t power;
mpz_t temp,temp2,temp3;

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

/* return 1 if probable prime, return 0 if composite.
   if composite, return fraction in *f.
   offs: where we're at compared to origin */
int isbigprime(mpz_t n,int mul,int offs,double *f) {
	double z;
	mpz_mul_si(temp3,n,mul);
	if(offs>0) mpz_add_ui(temp3,temp3,offs);
	else if(offs<0) mpz_sub_ui(temp3,temp3,-offs);
	if(!fermattest(temp3)) {
		/* fraction */
		z=mpz_get_d(temp3);
		*f=(z-mpz_get_d(res))/z;
		return 0;
	}
	if(mpz_tstbit(temp3,1)^(offs==-1)) {
		/* 2^temp3 == 1 (mod 2p-offs) */
		if(!eulerlagrangelifchitz(temp3,1,-offs)) {
			z=mpz_get_d(temp3);
			*f=(z-mpz_get_d(res))/z;
			return 0;
		}
	} else {
		/* 2^temp3 ==-1 (mod 2p-offs) */
		if(!eulerlagrangelifchitz(temp3,-1,-offs)) {
			z=mpz_get_d(temp3);
			*f=(z-mpz_get_d(res))/z;
			return 0;
		}
	}
	return 1;
}

/* stupid brute force version for sanity test */
int findchainstupid(mpz_t in,int offs,int inc,double *f) {
	int len=0;
	mpz_t p;
	mpz_init(p);
	if(offs<0) mpz_sub_ui(p,in,-offs);
	else if(offs>0) mpz_add_ui(p,in,offs);
	else mpz_set(p,in);
	if(!mpz_tstbit(p,0)) { *f=0; mpz_clear(p); return 0; }
	while(isbigprime(p,1,0,f)) {
		mpz_mul_si(p,p,2);
		if(inc<0) mpz_sub_ui(p,p,1);
		else mpz_add_ui(p,p,1);
		len++;
	}
	mpz_clear(p);
	return len;
}

double findsanity(mpz_t origin,int mul,int offs,int inc) {
	mpz_t p;
	double f;
	int len;
	mpz_init(p);
	mpz_mul_si(p,origin,mul);
	len=findchainstupid(p,offs,inc,&f);
	mpz_clear(p);
	return f+len;
}

int glo;

#define FIX \
	if(m1-lo>hi-m2) hi=m1,*f=g; \
	else lo=m2; \
	goto restart;

/* return length of longest chain between lo and hi.
   fraction f is -1 if end of chain isn't known yet.
   method: check numbers in the middle first */
/* base is origin*(1<<lo)+offs */
/* don't divide'n'conquer, always assume that chain is never split into two
   long enough chains */
int findchain(int base,int lo,int hi,int mask,mpz_t origin,int offs,double *f) {
	int len=hi-lo,mid,mid2,m1,m2,i,j;
	double g=0;
restart:
	len=hi-lo;
	if(len+1<MINACCEPT) return 0;
	mid=lo+(hi-lo)/2;
	/* middle element */
	if(len&1) mid2=mid+1;
	else {
		if(!(mask&(1<<mid)) && !isbigprime(origin,base<<mid,offs,&g)) {
			m1=mid-1;
			m2=mid+1;
			FIX
		} else mask|=1<<mid;
		mid2=mid--+1;
	}
	for(i=0;i<=mid-lo;i++) {
		j=mid-i;
		if(!(mask&(1<<j)) && !isbigprime(origin,base<<j,offs,&g)) {
			m1=j-1;
			m2=j+1;
			FIX
		} else mask|=1<<j;
		j=mid2+i;
		if(!(mask&(1<<j)) && !isbigprime(origin,base<<j,offs,&g)) {
			m1=j-1;
			m2=j+1;
			FIX
		} else mask|=1<<j;
	}
	/* chain ok */
	if(*f<-0.1) {
		isbigprime(origin,base<<(hi+1),offs,f);
		if(*f<-0.1) printf("bug");
	}
	glo=lo;
	printf("[%d %d] ",lo,hi);
	return hi-lo+1;
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

void work() {
	ll tried=0;
	int i,p,a,j,k,p2,l1,l2,l3,mask,errors=0;
	double start=gettime(),tid,f1,f2;
	double tidsieve=0,tidprim=0;
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
		tidsieve-=gettime();
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
		tidsieve+=gettime();
		/* find potential chains in sieve, primality test all numbers in chain
		   - only use as origins odd multiples of hash, or even multiples where
		     half of the multiple is composite in the sieve
		*/
		tidprim-=gettime();
		p2=1;
		for(i=0;i<MINCHAIN;i++) p2*=2;
		/* look for chains */
		for(i=1;i<SIEVESIZE/p2;i++) {
			l1=l2=f1=f2=0;
			/* don't bother to check unless chain is guaranteed to be of length 3
			   (warning, if is hardcoded to 6 - doesn't use macro */
			if((i&1) || sieveminus[i>>1]) {
				for(k=0;k<MINCHAIN;k++) if(sieveminus[i<<k]) goto failminus;
				k=MINCHAIN;
				mask=0;
				f1=-1;
#ifdef BEYOND
				while(1) {
					if((i<<k)<SIEVESIZE) {
						if(sieveminus[i<<k]) break;
					} else {
						if(isbigprime(origin,i<<k,-1,&f1)) mask|=1<<k;
						else break;
					}
					k++;
				}
#endif
				l1=findchain(i,0,k-1,mask,origin,-1,&f1);
			failminus:;
			}
			if((i&1) || sieveplus[i>>1]) {
				for(k=0;k<MINCHAIN;k++) if(sieveplus[i<<k]) goto failplus;
				mask=0;
				f2=-1;
#ifdef BEYOND
				while(1) {
					if((i<<k)<SIEVESIZE) {
						if(sieveplus[i<<k]) break;
					} else {
						if(isbigprime(origin,i<<k,1,&f2)) mask|=1<<k;
						else break;
					}
					k++;
				}
#endif
				l2=findchain(i,0,k-1,mask,origin,1,&f2);
			failplus:;
			}
			if(l1>l2) l3=l2+l2;
			else if(l1<l2) l3=l1+l1;
			else l3=l1+l2;
			if(l1) num[l1][0]++;
			if(l2) num[l2][1]++;
			if(l3) num[l3][2]++;
			if(l1>4) {
				printf("found chain type 1 length %.12f\n",l1+f1);
				if(fabs(l1+f1-findsanity(origin,i<<glo,-1,1))>1e-6) puts("error"),errors++;
			}
			if(l2>4) {
				printf("found chain type 2 length %.12f\n",l2+f2);
				if(fabs(l2+f2-findsanity(origin,i<<glo,1,-1))>1e-6) puts("error"),errors++;
			}
			/* don't know about fractional length here, just take average
			   (which is wrong, since it changes the distribution) */
			if(l3>4) printf("found chain type 3 length %.12f\n",l3+(f1+f2)*.5);
		}
		tidprim+=gettime();
		f1=tidprim+tidsieve;
		if(tried%500==0) {
			tid=gettime();
			puts("===============================================================================");
			printf("after trying %I64d hashes (%.4f sieve, %.4f primcheck):\n",tried,tidsieve/f1,tidprim/f1);
			for(i=3;i<50;i++) if(num[i][0]+num[i][1]+num[i][2]) {
				printf(" %2dch/h: %9.2f [%I64d %I64d %I64d]\n",i,
					(num[i][0]+num[i][1]+num[i][2])/((tid-start)/3600),num[i][0],num[i][1],num[i][2]);
			}
			if(errors) printf("ERRORS FOUND %d\n",errors);
			puts("===============================================================================");
		}
	}
}

void test(char *s) {
	mpz_t p;
	int len;
	double f;
	mpz_init_set_str(p,s,10);
	len=findchainstupid(p,0,1,&f);
	printf("try %s:\n",s);
	printf("  found %.12f\n",len+f);
	len=findchainstupid(p,0,-1,&f);
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
	mpz_init(temp2);
	mpz_init(temp3);
	sanity();
	work();
	return 0;
}
