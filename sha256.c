#include <stdio.h>
#include <string.h>
/* naive implementation of sha-256 */
#define MAXSTR 1000000
#define ROR(v,len) ((v<<(32-len))+(v>>len))
#define OUTPUT(a,ix,v) a[ix]=(v)>>24; a[ix+1]=((v)>>16)&255; a[ix+2]=((v)>>8)&255; a[ix+3]=(v)&255
void sha256(unsigned char *s,int len,unsigned char *out) {
	unsigned int h0,h1,h2,h3,h4,h5,h6,h7;
	unsigned int k[64]={0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
		0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01,
		0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
		0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa,
		0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
		0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138,
		0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
		0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 
		0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
		0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f,
		0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
	static unsigned char msg[MAXSTR];
	int i,z;
	unsigned int a,b,c,d,e,f,g,h,s0,s1,ch,temp1,temp2,maj,n=len<<3;
	h0=0x6a09e667; h1=0xbb67ae85; h2=0x3c6ef372; h3=0xa54ff53a;
	h4=0x510e527f; h5=0x9b05688c; h6=0x1f83d9ab; h7=0x5be0cd19;
	if(len>MAXSTR-66) { printf("error"); return; }
	for(i=0;i<len;i++) msg[i]=s[i];
	msg[len++]=0x80;
	while((len&63)!=56) msg[len++]=0;
	msg[len++]=0; msg[len++]=0; msg[len++]=0; msg[len++]=0;
	msg[len++]=(n>>24)&255; msg[len++]=(n>>16)&255;
	msg[len++]=(n>>8)&255; msg[len++]=n&255;
	for(z=0;z<len;z+=64) {
		unsigned int w[64];
		for(i=0;i<16;i++) w[i]=(msg[z+i*4]<<24)+(msg[z+i*4+1]<<16)+(msg[z+i*4+2]<<8)+msg[z+i*4+3];
		for(i=16;i<64;i++) {
			s0=ROR(w[i-15],7)^ROR(w[i-15],18)^(w[i-15]>>3);
			s1=ROR(w[i-2],17)^ROR(w[i-2],19)^(w[i-2]>>10);
			w[i]=w[i-16]+s0+w[i-7]+s1;
			a=h0; b=h1; c=h2; d=h3; e=h4; f=h5; g=h6; h=h7;
		}
		for(i=0;i<64;i++) {
			s1=ROR(e,6)^ROR(e,11)^ROR(e,25);
			ch=(e&f)^((~e)&g);
			temp1=h+s1+ch+k[i]+w[i];
			s0=ROR(a,2)^ROR(a,13)^ROR(a,22);
			maj=(a&b)^(a&c)^(b&c);
			temp2=s0+maj;
			h=g; g=f; f=e; e=d+temp1;
			d=c; c=b; b=a; a=temp1+temp2;
		}
		h0+=a; h1+=b; h2+=c; h3+=d; h4+=e; h5+=f; h6+=g; h7+=h;
	}
	OUTPUT(out,0,h0); OUTPUT(out,4,h1); OUTPUT(out,8,h2); OUTPUT(out,12,h3);
	OUTPUT(out,16,h4); OUTPUT(out,20,h5); OUTPUT(out,24,h6); OUTPUT(out,28,h7);
}
