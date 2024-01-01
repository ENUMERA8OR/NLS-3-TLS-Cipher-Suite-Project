#include <iostream>
 

#include "ns3/lte-helper.h"
#include "ns3/epc-helper.h"
#include "ns3/core-module.h"
#include "ns3/network-module.h"
#include "ns3/ipv4-global-routing-helper.h"
#include "ns3/internet-module.h"
#include "ns3/mobility-module.h"
#include "ns3/lte-module.h"
#include "ns3/applications-module.h"
#include "ns3/point-to-point-helper.h"
#include "ns3/config-store.h"
#include <ns3/buildings-module.h>
#include "ns3/netanim-module.h"
#include "ns3/gnuplot.h"
#include "ns3/flow-monitor-module.h"
#include "ns3/log.h"
#include <sys/timeb.h>
#include <ns3/internet-trace-helper.h>
#include <ns3/spectrum-module.h>
#include <ns3/log.h>
#include <ns3/string.h>
#include <fstream>


#include "ns3/aodv-module.h"
#include "ns3/netanim-module.h"
#include "ns3/core-module.h"
#include "ns3/network-module.h"
#include "ns3/internet-module.h"
#include "ns3/applications-module.h"
#include "ns3/mobility-module.h"
#include "ns3/wifi-module.h"
#include "ns3/mesh-module.h"
#include "ns3/ipv4-global-routing-helper.h"
#include "ns3/olsr-helper.h"
#include "ns3/point-to-point-module.h"
#include "ns3/csma-module.h"
#include "ns3/netanim-module.h"
#include "ns3/flow-monitor-module.h"
#include "ns3/mobility-module.h"
#include "myapp.h"
#include "ns3/simulator.h"
#include "ns3/nstime.h"
#include "ns3/command-line.h"
#include "ns3/random-variable-stream.h"


#include "ns3/flow-monitor-helper.h"
#include "ns3/gnuplot.h"

#include <iostream>
#include <sstream>
#include <fstream>

#include <string.h> // CBC mode, for memset
#include "aes.h"
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include<stdio.h>
#include<string.h>
#include<malloc.h>
#include<math.h>
#include<stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "bloom.h"

#define rotateleft(x,n) ((x<<n) | (x>>(32-n)))
#define rotateright(x,n) ((x>>n) | (x<<(32-n)))
#define CBC 1
#define CTR 1
#define ECB 1

#include <iostream>
#include <cmath>
#include "ns3/core-module.h"
#include "ns3/network-module.h"
#include "ns3/applications-module.h"
#include "ns3/mobility-module.h"
#include "ns3/config-store-module.h"
#include "ns3/internet-module.h"
#include "ns3/dsdv-helper.h"
#include "ns3/yans-wifi-helper.h"
#include "ns3/gnuplot.h"
#include "ns3/netanim-module.h"


using namespace ns3;

uint16_t port = 9;

//NS_LOG_COMPONENT_DEFINE ("crypto");

NS_LOG_COMPONENT_DEFINE ("crypto");




static void phex(uint8_t* str);
static int test_encrypt_cbc(void);
static int test_decrypt_cbc(void);
static int test_encrypt_ctr(void);
static int test_decrypt_ctr(void);
static int test_encrypt_ecb(void);
static int test_decrypt_ecb(void);
static void test_encrypt_ecb_verbose(void);

//using namespace ns3;
    int       m_xSize=3;
    int       m_ySize=3;
    int       m_sta=1;
    int       m_ap=1;
    uint16_t  m_packetSize=1024;
    uint16_t  m_NumOfPacket=50;

int packetCount,received_bits=0,transmitted_bits=0;
float throughput,localThrou,pdf;
float first_transmittedpacket,last_transmittedpacket,sum_of_ete_delay;

FlowMonitorHelper flowmon;
Ptr<FlowMonitor> monitor;

uint64_t simulationTime = 60; //seconds

double TotalTime = 120.0;
  std::string rate ("2048bps");
  std::string phyMode ("DsssRate11Mbps");
  std::string tr_name ("GRAY");
  int nodeSpeed = 20; //in m/s
  int nodePause = 0; //in s
//  m_protocolName = "protocol";



#define Nb 4

#if defined(AES256) && (AES256 == 1)
    #define Nk 8
    #define Nr 14
#elif defined(AES192) && (AES192 == 1)
    #define Nk 6
    #define Nr 12
#else
    #define Nk 4        // The number of 32 bit words in a key.
    #define Nr 10       // The number of rounds in AES Cipher.
#endif
#ifndef MULTIPLY_AS_A_FUNCTION
  #define MULTIPLY_AS_A_FUNCTION 0
#endif
struct bloom_hash {
    hash_function func;
    struct bloom_hash *next;
};

struct bloom_filter {
    struct bloom_hash *func;
    uint8_t *bits;
    size_t size;
};

typedef uint8_t state_t[4][4];
static const uint8_t sbox[256] = {
  //0     1    2      3     4    5     6     7      8    9     A      B    C     D     E     F
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 };

static const uint8_t rsbox[256] = {
  0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
  0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
  0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
  0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
  0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
  0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
  0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
  0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
  0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
  0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
  0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
  0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
  0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
  0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
  0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
  0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d };
static const uint8_t Rcon[11] = {
  0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36 };

#define getSBoxValue(num) (sbox[(num)])
#define getSBoxInvert(num) (rsbox[(num)])
bloom_t bloom_create(size_t size) 
{
	bloom_filter *res;
	res=(struct bloom_filter *)malloc(1 * sizeof(struct bloom_filter));
	res->size = size;
	//res->bits = 666;
	return res;
}

void bloom_free(bloom_t filter) {
	if (filter) {
		while (filter->func) {
			struct bloom_hash *h = filter->func;
			filter->func = h->next;
			free(h);
		}
		free(filter->bits);
		free(filter);
	}
}

void bloom_add_hash(bloom_t filter, hash_function func) 
{
	struct bloom_hash *h;
        h=(struct bloom_hash *)malloc(1 * sizeof(struct bloom_hash));
	h->func = func;
	struct bloom_hash *last = filter->func;
	while (last && last->next) {
		last = last->next;
	}
	if (last) {
		last->next = h;
	} else {
		filter->func = h;
	}
}

void bloom_add(bloom_t filter, const void *item) {
	struct bloom_hash *h = filter->func;
	uint8_t *bits = filter->bits;
	while (h) {
		unsigned int hash = h->func(item);
		hash %= filter->size * 8;
		bits[hash / 8] |= 1 << hash % 8;
		h = h->next;
	}
}

bool bloom_test(bloom_t filter, const void *item) {
	struct bloom_hash *h = filter->func;
	uint8_t *bits = filter->bits;
	while (h) {
		unsigned int hash = h->func(item);
		hash %= filter->size * 8;
		if (!(bits[hash / 8] & 1 << hash % 8)) {
			return false;
		}
		h = h->next;
	}
	return true;
}
unsigned int djb2(const char *_str) {
	const char *str = _str;
	unsigned int hash = 5381;
	char c;
	while ((c = *str++)) {
		hash = ((hash << 5) + hash) + c;
	}
	return hash;
}

unsigned int jenkins(const char *_str) {
	const char *key = _str;
	unsigned int hash;
	while (*key) {
		hash += *key;
		hash += (hash << 10);
		hash ^= (hash >> 6);
		key++;
	}
	hash += (hash << 3);
	hash ^= (hash >> 11);
	hash += (hash << 15);
	return hash;
}
void SHA1(unsigned char * str1)
{
unsigned int h0,h1,h2,h3,h4,a,b,c,d,e,f,k,temp;
h0 = 0x67452301;
h1 = 0xEFCDAB89;
h2 = 0x98BADCFE;
h3 = 0x10325476;
h4 = 0xC3D2E1F0;
unsigned char * str;
str = (unsigned char *)malloc(strlen((const char *)str1)+100);
strcpy((char *)str,(const char *)str1);
int current_length = strlen((const char *)str);
int original_length = current_length;
str[current_length] = 0x80;
str[current_length + 1] = '\0';
char ic = str[current_length];
current_length++;
int ib = current_length % 64;
if(ib<56)
ib = 56-ib;
else
ib = 120 - ib;
int i;
for( i=0;i < ib;i++)
{
str[current_length]=0x00;
current_length++;
}
str[current_length + 1]='\0';
for( i=0;i<6;i++)
{
str[current_length]=0x0;
current_length++;
}
str[current_length] = (original_length * 8) / 0x100 ;
current_length++;
str[current_length] = (original_length * 8) % 0x100;
current_length++;
str[current_length+i]='\0';
int number_of_chunks = current_length/64;
unsigned long int word[80];
int j;
for(i=0;i<number_of_chunks;i++)
{
for( j=0;j<16;j++)
{
word[j] = str[i*64 + j*4 + 0] * 0x1000000 + str[i*64 + j*4 + 1] * 0x10000 + str[i*64 + j*4 + 2] * 0x100 + str[i*64 + j*4 + 3];
}
for( j=16;j<80;j++)
{
word[j] = rotateleft((word[j-3] ^ word[j-8] ^ word[j-14] ^ word[j-16]),1);
}
a = h0;
b = h1;
c = h2;
d = h3;
e = h4;
for(int m=0;m<80;m++)
{
if(m<=19)
{
f = (b & c) | ((~b) & d);
k = 0x5A827999;
}
else if(m<=39)
{
f = b ^ c ^ d;
k = 0x6ED9EBA1;
}
else if(m<=59)
{
f = (b & c) | (b & d) | (c & d);
k = 0x8F1BBCDC;
}
else
{
f = b ^ c ^ d;
k = 0xCA62C1D6;
}
temp = (rotateleft(a,5) + f + e + k + word[m]) & 0xFFFFFFFF;
e = d;
d = c;
c = rotateleft(b,30);
b = a;
a = temp;
}
h0 = h0 + a;
h1 = h1 + b;
h2 = h2 + c;
h3 = h3 + d;
h4 = h4 + e;
}
printf("\n\n");
printf("Hash: %x %x %x %x %x",h0, h1, h2, h3, h4);
printf("\n\n");

printf("%c",ic);
}
static void KeyExpansion(uint8_t* RoundKey, const uint8_t* Key)
{
  unsigned i, j, k;
  uint8_t tempa[4]; // Used for the column/row operations
  
  // The first round key is the key itself.
  for (i = 0; i < Nk; ++i)
  {
    RoundKey[(i * 4) + 0] = Key[(i * 4) + 0];
    RoundKey[(i * 4) + 1] = Key[(i * 4) + 1];
    RoundKey[(i * 4) + 2] = Key[(i * 4) + 2];
    RoundKey[(i * 4) + 3] = Key[(i * 4) + 3];
  }

  // All other round keys are found from the previous round keys.
  for (i = Nk; i < Nb * (Nr + 1); ++i)
  {
    {
      k = (i - 1) * 4;
      tempa[0]=RoundKey[k + 0];
      tempa[1]=RoundKey[k + 1];
      tempa[2]=RoundKey[k + 2];
      tempa[3]=RoundKey[k + 3];

    }

    if (i % Nk == 0)
    {
      // This function shifts the 4 bytes in a word to the left once.
      // [a0,a1,a2,a3] becomes [a1,a2,a3,a0]

      // Function RotWord()
      {
        const uint8_t u8tmp = tempa[0];
        tempa[0] = tempa[1];
        tempa[1] = tempa[2];
        tempa[2] = tempa[3];
        tempa[3] = u8tmp;
      }

      // SubWord() is a function that takes a four-byte input word and 
      // applies the S-box to each of the four bytes to produce an output word.

      // Function Subword()
      {
        tempa[0] = getSBoxValue(tempa[0]);
        tempa[1] = getSBoxValue(tempa[1]);
        tempa[2] = getSBoxValue(tempa[2]);
        tempa[3] = getSBoxValue(tempa[3]);
      }

      tempa[0] = tempa[0] ^ Rcon[i/Nk];
    }
#if defined(AES256) && (AES256 == 1)
    if (i % Nk == 4)
    {
      // Function Subword()
      {
        tempa[0] = getSBoxValue(tempa[0]);
        tempa[1] = getSBoxValue(tempa[1]);
        tempa[2] = getSBoxValue(tempa[2]);
        tempa[3] = getSBoxValue(tempa[3]);
      }
    }
#endif
    j = i * 4; k=(i - Nk) * 4;
    RoundKey[j + 0] = RoundKey[k + 0] ^ tempa[0];
    RoundKey[j + 1] = RoundKey[k + 1] ^ tempa[1];
    RoundKey[j + 2] = RoundKey[k + 2] ^ tempa[2];
    RoundKey[j + 3] = RoundKey[k + 3] ^ tempa[3];
  }
}

void AES_init_ctx(struct AES_ctx* ctx, const uint8_t* key)
{
  KeyExpansion(ctx->RoundKey, key);
}
#if (defined(CBC) && (CBC == 1)) || (defined(CTR) && (CTR == 1))
void AES_init_ctx_iv(struct AES_ctx* ctx, const uint8_t* key, const uint8_t* iv)
{
  KeyExpansion(ctx->RoundKey, key);
  memcpy (ctx->Iv, iv, AES_BLOCKLEN);
}
void AES_ctx_set_iv(struct AES_ctx* ctx, const uint8_t* iv)
{
  memcpy (ctx->Iv, iv, AES_BLOCKLEN);
}
#endif

// This function adds the round key to state.
// The round key is added to the state by an XOR function.
static void AddRoundKey(uint8_t round, state_t* state, const uint8_t* RoundKey)
{
  uint8_t i,j;
  for (i = 0; i < 4; ++i)
  {
    for (j = 0; j < 4; ++j)
    {
      (*state)[i][j] ^= RoundKey[(round * Nb * 4) + (i * Nb) + j];
    }
  }
}

// The SubBytes Function Substitutes the values in the
// state matrix with values in an S-box.
static void SubBytes(state_t* state)
{
  uint8_t i, j;
  for (i = 0; i < 4; ++i)
  {
    for (j = 0; j < 4; ++j)
    {
      (*state)[j][i] = getSBoxValue((*state)[j][i]);
    }
  }
}
static void ShiftRows(state_t* state)
{
  uint8_t temp;

  // Rotate first row 1 columns to left  
  temp           = (*state)[0][1];
  (*state)[0][1] = (*state)[1][1];
  (*state)[1][1] = (*state)[2][1];
  (*state)[2][1] = (*state)[3][1];
  (*state)[3][1] = temp;

  // Rotate second row 2 columns to left  
  temp           = (*state)[0][2];
  (*state)[0][2] = (*state)[2][2];
  (*state)[2][2] = temp;

  temp           = (*state)[1][2];
  (*state)[1][2] = (*state)[3][2];
  (*state)[3][2] = temp;

  // Rotate third row 3 columns to left
  temp           = (*state)[0][3];
  (*state)[0][3] = (*state)[3][3];
  (*state)[3][3] = (*state)[2][3];
  (*state)[2][3] = (*state)[1][3];
  (*state)[1][3] = temp;
}

static uint8_t xtime(uint8_t x)
{
  return ((x<<1) ^ (((x>>7) & 1) * 0x1b));
}

// MixColumns function mixes the columns of the state matrix
static void MixColumns(state_t* state)
{
  uint8_t i;
  uint8_t Tmp, Tm, t;
  for (i = 0; i < 4; ++i)
  {  
    t   = (*state)[i][0];
    Tmp = (*state)[i][0] ^ (*state)[i][1] ^ (*state)[i][2] ^ (*state)[i][3] ;
    Tm  = (*state)[i][0] ^ (*state)[i][1] ; Tm = xtime(Tm);  (*state)[i][0] ^= Tm ^ Tmp ;
    Tm  = (*state)[i][1] ^ (*state)[i][2] ; Tm = xtime(Tm);  (*state)[i][1] ^= Tm ^ Tmp ;
    Tm  = (*state)[i][2] ^ (*state)[i][3] ; Tm = xtime(Tm);  (*state)[i][2] ^= Tm ^ Tmp ;
    Tm  = (*state)[i][3] ^ t ;              Tm = xtime(Tm);  (*state)[i][3] ^= Tm ^ Tmp ;
  }
}

// Multiply is used to multiply numbers in the field GF(2^8)
// Note: The last call to xtime() is unneeded, but often ends up generating a smaller binary
//       The compiler seems to be able to vectorize the operation better this way.
//       See https://github.com/kokke/tiny-AES-c/pull/34
#if MULTIPLY_AS_A_FUNCTION
static uint8_t Multiply(uint8_t x, uint8_t y)
{
  return (((y & 1) * x) ^
       ((y>>1 & 1) * xtime(x)) ^
       ((y>>2 & 1) * xtime(xtime(x))) ^
       ((y>>3 & 1) * xtime(xtime(xtime(x)))) ^
       ((y>>4 & 1) * xtime(xtime(xtime(xtime(x)))))); /* this last call to xtime() can be omitted */
  }
#else
#define Multiply(x, y)                                \
      (  ((y & 1) * x) ^                              \
      ((y>>1 & 1) * xtime(x)) ^                       \
      ((y>>2 & 1) * xtime(xtime(x))) ^                \
      ((y>>3 & 1) * xtime(xtime(xtime(x)))) ^         \
      ((y>>4 & 1) * xtime(xtime(xtime(xtime(x))))))   \

#endif

#if (defined(CBC) && CBC == 1) || (defined(ECB) && ECB == 1)
// MixColumns function mixes the columns of the state matrix.
// The method used to multiply may be difficult to understand for the inexperienced.
// Please use the references to gain more information.
static void InvMixColumns(state_t* state)
{
  int i;
  uint8_t a, b, c, d;
  for (i = 0; i < 4; ++i)
  { 
    a = (*state)[i][0];
    b = (*state)[i][1];
    c = (*state)[i][2];
    d = (*state)[i][3];

    (*state)[i][0] = Multiply(a, 0x0e) ^ Multiply(b, 0x0b) ^ Multiply(c, 0x0d) ^ Multiply(d, 0x09);
    (*state)[i][1] = Multiply(a, 0x09) ^ Multiply(b, 0x0e) ^ Multiply(c, 0x0b) ^ Multiply(d, 0x0d);
    (*state)[i][2] = Multiply(a, 0x0d) ^ Multiply(b, 0x09) ^ Multiply(c, 0x0e) ^ Multiply(d, 0x0b);
    (*state)[i][3] = Multiply(a, 0x0b) ^ Multiply(b, 0x0d) ^ Multiply(c, 0x09) ^ Multiply(d, 0x0e);
  }
}


// The SubBytes Function Substitutes the values in the
// state matrix with values in an S-box.
static void InvSubBytes(state_t* state)
{
  uint8_t i, j;
  for (i = 0; i < 4; ++i)
  {
    for (j = 0; j < 4; ++j)
    {
      (*state)[j][i] = getSBoxInvert((*state)[j][i]);
    }
  }
}

static void InvShiftRows(state_t* state)
{
  uint8_t temp;

  // Rotate first row 1 columns to right  
  temp = (*state)[3][1];
  (*state)[3][1] = (*state)[2][1];
  (*state)[2][1] = (*state)[1][1];
  (*state)[1][1] = (*state)[0][1];
  (*state)[0][1] = temp;

  // Rotate second row 2 columns to right 
  temp = (*state)[0][2];
  (*state)[0][2] = (*state)[2][2];
  (*state)[2][2] = temp;

  temp = (*state)[1][2];
  (*state)[1][2] = (*state)[3][2];
  (*state)[3][2] = temp;

  // Rotate third row 3 columns to right
  temp = (*state)[0][3];
  (*state)[0][3] = (*state)[1][3];
  (*state)[1][3] = (*state)[2][3];
  (*state)[2][3] = (*state)[3][3];
  (*state)[3][3] = temp;
}
#endif // #if (defined(CBC) && CBC == 1) || (defined(ECB) && ECB == 1)

// Cipher is the main function that encrypts the PlainText.
static void Cipher(state_t* state, const uint8_t* RoundKey)
{
  uint8_t round = 0;

  // Add the First round key to the state before starting the rounds.
  AddRoundKey(0, state, RoundKey);

  // There will be Nr rounds.
  // The first Nr-1 rounds are identical.
  // These Nr rounds are executed in the loop below.
  // Last one without MixColumns()
  for (round = 1; ; ++round)
  {
    SubBytes(state);
    ShiftRows(state);
    if (round == Nr) {
      break;
    }
    MixColumns(state);
    AddRoundKey(round, state, RoundKey);
  }
  // Add round key to last round
  AddRoundKey(Nr, state, RoundKey);
}

#if (defined(CBC) && CBC == 1) || (defined(ECB) && ECB == 1)
static void InvCipher(state_t* state, const uint8_t* RoundKey)
{
  uint8_t round = 0;

  // Add the First round key to the state before starting the rounds.
  AddRoundKey(Nr, state, RoundKey);

  // There will be Nr rounds.
  // The first Nr-1 rounds are identical.
  // These Nr rounds are executed in the loop below.
  // Last one without InvMixColumn()
  for (round = (Nr - 1); ; --round)
  {
    InvShiftRows(state);
    InvSubBytes(state);
    AddRoundKey(round, state, RoundKey);
    if (round == 0) {
      break;
    }
    InvMixColumns(state);
  }

}
#endif // #if (defined(CBC) && CBC == 1) || (defined(ECB) && ECB == 1)

/*****************************************************************************/
/* Public functions:                                                         */
/*****************************************************************************/
#if defined(ECB) && (ECB == 1)


void AES_ECB_encrypt(const struct AES_ctx* ctx, uint8_t* buf)
{
  // The next function call encrypts the PlainText with the Key using AES algorithm.
  Cipher((state_t*)buf, ctx->RoundKey);
}

void AES_ECB_decrypt(const struct AES_ctx* ctx, uint8_t* buf)
{
  // The next function call decrypts the PlainText with the Key using AES algorithm.
  InvCipher((state_t*)buf, ctx->RoundKey);
}


#endif // #if defined(ECB) && (ECB == 1)





#if defined(CBC) && (CBC == 1)


static void XorWithIv(uint8_t* buf, const uint8_t* Iv)
{
  uint8_t i;
  for (i = 0; i < AES_BLOCKLEN; ++i) // The block in AES is always 128bit no matter the key size
  {
    buf[i] ^= Iv[i];
  }
}

void AES_CBC_encrypt_buffer(struct AES_ctx *ctx, uint8_t* buf, uint32_t length)
{
  uintptr_t i;
  uint8_t *Iv = ctx->Iv;
  for (i = 0; i < length; i += AES_BLOCKLEN)
  {
    XorWithIv(buf, Iv);
    Cipher((state_t*)buf, ctx->RoundKey);
    Iv = buf;
    buf += AES_BLOCKLEN;
  }
  /* store Iv in ctx for next call */
  memcpy(ctx->Iv, Iv, AES_BLOCKLEN);
}

void AES_CBC_decrypt_buffer(struct AES_ctx* ctx, uint8_t* buf,  uint32_t length)
{
  uintptr_t i;
  uint8_t storeNextIv[AES_BLOCKLEN];
  for (i = 0; i < length; i += AES_BLOCKLEN)
  {
    memcpy(storeNextIv, buf, AES_BLOCKLEN);
    InvCipher((state_t*)buf, ctx->RoundKey);
    XorWithIv(buf, ctx->Iv);
    memcpy(ctx->Iv, storeNextIv, AES_BLOCKLEN);
    buf += AES_BLOCKLEN;
  }

}

#endif // #if defined(CBC) && (CBC == 1)



#if defined(CTR) && (CTR == 1)

/* Symmetrical operation: same function for encrypting as for decrypting. Note any IV/nonce should never be reused with the same key */
void AES_CTR_xcrypt_buffer(struct AES_ctx* ctx, uint8_t* buf, uint32_t length)
{
  uint8_t buffer[AES_BLOCKLEN];
  
  unsigned i;
  int bi;
  for (i = 0, bi = AES_BLOCKLEN; i < length; ++i, ++bi)
  {
    if (bi == AES_BLOCKLEN) /* we need to regen xor compliment in buffer */
    {
      
      memcpy(buffer, ctx->Iv, AES_BLOCKLEN);
      Cipher((state_t*)buffer,ctx->RoundKey);

      /* Increment Iv and handle overflow */
      for (bi = (AES_BLOCKLEN - 1); bi >= 0; --bi)
      {
	/* inc will overflow */
        if (ctx->Iv[bi] == 255)
	{
          ctx->Iv[bi] = 0;
          continue;
        } 
        ctx->Iv[bi] += 1;
        break;   
      }
      bi = 0;
    }

    buf[i] = (buf[i] ^ buffer[bi]);
  }
}

#endif // #if defined(CTR) && (CTR == 1)

int drop_packet=5;
float random_value1,random_value2,random_value3,random_value4,random_value5;  
int  random_value11,random_value22,random_value33,random_value44,random_value55; 
 
void ReceivePacket(Ptr<const Packet> p, const Address & addr)
{
    InetSocketAddress transport = InetSocketAddress::ConvertFrom (addr);

    if(packetCount==1)
    {
        first_transmittedpacket=Simulator::Now ().GetSeconds ();
    }   

  if(transport.GetIpv4 () == "10.1.2.7")
 {
     if(random_value11==packetCount)
    {
      std::cout<<"Malicious Node in wireless  network:: Packet dropped!!!"<<std::endl;
      packetCount++;      
     }
    else if(random_value22==packetCount)
    {
      std::cout<<"Malicious Node in wireless  network:: Packet dropped!!!"<<std::endl;
      packetCount++;      
     }
    else if(random_value33==packetCount)
    {

      std::cout<<"Malicious Node in wireless  network:: Packet dropped!!!"<<std::endl;
      packetCount++;      
     }
    else if(random_value44==packetCount)
    {

      std::cout<<"Malicious Node in wireless  network:: Packet dropped!!!"<<std::endl;
      packetCount++;
     }
    else if(random_value55==packetCount)
    {
      std::cout<<"Malicious Node in wireless  network:: Packet dropped!!!"<<std::endl;
      packetCount++;
     }
     else
     {
      packetCount++;
      std::cout << packetCount << "\t" << Simulator::Now ().GetSeconds () << "\t" << p->GetSize() <<"\n";
      if(packetCount==m_NumOfPacket)
    {

        last_transmittedpacket=Simulator::Now ().GetSeconds ();
        sum_of_ete_delay=last_transmittedpacket - first_transmittedpacket;

        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Total Sent Packet="<<m_NumOfPacket<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Total Received Packet="<<(packetCount-drop_packet)<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "Duration    : " <<Simulator::Now ().GetSeconds ()<< "Seconds" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "transmitted bits : " <<transmitted_bits<< "bits" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "received bits : " <<(received_bits-(1024*drop_packet))<< "bits" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "Throughput    : " << (received_bits-(1024*drop_packet))/(Simulator::Now ().GetSeconds () - first_transmittedpacket)/1024/1024 << " Mbps" <<std::endl;

        pdf = (double)(packetCount-drop_packet)/m_NumOfPacket;

        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Avereage End to End Delay = "<<sum_of_ete_delay*1000/(packetCount-drop_packet)<<"ms"<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Average Packet Delivery Fraction = "<<pdf<<""<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Percentage of Packet loss = "<<(1-pdf)*100<<"%"<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        packetCount=0;
        transmitted_bits=0;
        received_bits=0;
        sum_of_ete_delay=0;
bloom_t bloom = bloom_create(8);
       printf("Created Bloom filter");
       printf("Bloom Bits %p",bloom->bits);
	
int exit;

#if defined(AES256)
    printf("\nTesting AES256\n\n");
#elif defined(AES192)
    printf("\nTesting AES192\n\n");
#elif defined(AES128)
    printf("\nTesting AES128\n\n");
#else
    printf("You need to specify a symbol between AES128, AES192 or AES256. Exiting");
    return 0;
#endif

    exit = test_encrypt_cbc() + test_decrypt_cbc() +
	test_encrypt_ctr() + test_decrypt_ctr() +
	test_decrypt_ecb() + test_encrypt_ecb();
    test_encrypt_ecb_verbose();
printf("%d",exit);
printf("Executing SHA.......\n");
SHA1((unsigned char *)"The quick brown fox jumps over the lazy dog");


     return;
    }
     }

    transmitted_bits+=p->GetSize()*8;
    received_bits+=p->GetSize()*8;
}
 else if((transport.GetIpv4 () == "10.1.2.6") || (transport.GetIpv4 () == "20.1.3.1"))
 {
      packetCount++;
      std::cout << packetCount << "\t" << Simulator::Now ().GetSeconds () << "\t" << p->GetSize() <<"\n";
      if(packetCount==(m_NumOfPacket-drop_packet))
    {

        last_transmittedpacket=Simulator::Now ().GetSeconds ();
        sum_of_ete_delay=last_transmittedpacket - first_transmittedpacket;

        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Total Sent Packet="<<m_NumOfPacket-drop_packet<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Total Received Packet="<<(packetCount)<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "Duration    : " <<Simulator::Now ().GetSeconds ()<< "Seconds" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "transmitted bits : " <<transmitted_bits<< "bits" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "received bits : " <<(received_bits)<< "bits" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "Throughput    : " << (received_bits)/(Simulator::Now ().GetSeconds () - first_transmittedpacket)/1024/1024 << " Mbps" <<std::endl;

        pdf = (double)(packetCount/(m_NumOfPacket-drop_packet));

        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Avereage End to End Delay = "<<sum_of_ete_delay*1000/(packetCount-drop_packet)<<"ms"<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Average Packet Delivery Fraction = "<<pdf<<""<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Percentage of Packet loss = "<<(1-pdf)*100<<"%"<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        packetCount=0;
        transmitted_bits=0;
        received_bits=0;
        sum_of_ete_delay=0;
bloom_t bloom = bloom_create(8);
       printf("Created Bloom filter");
       printf("Bloom Bits %p",bloom->bits);
     return;
    }

    transmitted_bits+=p->GetSize()*8;
    received_bits+=p->GetSize()*8;
}
else
{
      packetCount++;
      std::cout << packetCount << "\t" << Simulator::Now ().GetSeconds () << "\t" << p->GetSize() <<"\n";
      if(packetCount==m_NumOfPacket)
    {
        last_transmittedpacket=Simulator::Now ().GetSeconds ();
        sum_of_ete_delay=last_transmittedpacket - first_transmittedpacket;

        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Total Sent Packet="<<m_NumOfPacket<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Total Received Packet="<<(packetCount)<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "Duration    : " <<Simulator::Now ().GetSeconds ()<< "Seconds" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "transmitted bits : " <<transmitted_bits<< "bits" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "received bits : " <<(received_bits)<< "bits" << std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout << "Throughput    : " << (received_bits)/(Simulator::Now ().GetSeconds () - first_transmittedpacket)/1024/1024 << " Mbps" <<std::endl;

        pdf = (double)(packetCount)/m_NumOfPacket;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Avereage End to End Delay = "<<sum_of_ete_delay*1000/(packetCount)<<"ms"<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Average Packet Delivery Fraction = "<<pdf<<""<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        std::cout<<"Percentage of Packet loss = "<<(1-pdf)*100<<"%"<<std::endl;
        std::cout<<"*************************************"<<std::endl;
        packetCount=0;
        transmitted_bits=0;
        received_bits=0;
bloom_t bloom = bloom_create(8);
       printf("Created Bloom filter");
       printf("Bloom Bits %p",bloom->bits);
int exit;

#if defined(AES256)
    printf("\nTesting AES256\n\n");
#elif defined(AES192)
    printf("\nTesting AES192\n\n");
#elif defined(AES128)
    printf("\nTesting AES128\n\n");
#else
    printf("You need to specify a symbol between AES128, AES192 or AES256. Exiting");
    return 0;
#endif

    exit = test_encrypt_cbc() + test_decrypt_cbc() +
	test_encrypt_ctr() + test_decrypt_ctr() +
	test_decrypt_ecb() + test_encrypt_ecb();
    test_encrypt_ecb_verbose();
printf("%d",exit);
printf("Executing SHA.......\n");
SHA1((unsigned char *)"The quick brown fox jumps over the lazy dog");

     return;
    }
     }

    transmitted_bits+=p->GetSize()*8;
    received_bits+=p->GetSize()*8;
}





void
PrintGnuplottableUeListToFile (std::string filename)
{
  std::ofstream outFile;
  outFile.open (filename.c_str (), std::ios_base::out | std::ios_base::trunc);
  if (!outFile.is_open ())
    {
      NS_LOG_ERROR ("Can't open file " << filename);
      return;
    }
  for (NodeList::Iterator it = NodeList::Begin (); it != NodeList::End (); ++it)
    {
      Ptr<Node> node = *it;
      int nDevs = node->GetNDevices ();
      for (int j = 0; j < nDevs; j++)
        {
          Ptr<LteUeNetDevice> uedev = node->GetDevice (j)->GetObject <LteUeNetDevice> ();
          if (uedev)
            {
              Vector pos = node->GetObject<MobilityModel> ()->GetPosition ();
              outFile << "set label \"" << uedev->GetImsi ()
                      << "\" at " << pos.x << "," << pos.y << " left font \"Helvetica,4\" textcolor rgb \"grey\" front point pt 1 ps 0.3 lc rgb \"grey\" offset 0,0"
                      << std::endl;
            }
        }
    }
}





/**
 * \ingroup dsdv
 * \ingroup dsdv-examples
 * \ingroup examples
 *
 * \brief DSDV Manet example
 */
 
class DsdvManetExample
{
public:
  DsdvManetExample ();
  /**
   * Run function
   * \param nWifis The total number of nodes
   * \param nSinks The total number of receivers
   * \param totalTime The total simulation time
   * \param rate The network speed
   * \param phyMode The physical mode
   * \param nodeSpeed The node speed
   * \param periodicUpdateInterval The routing update interval
   * \param settlingTime The routing update settling time
   * \param dataStart The data transmission start time
   * \param printRoutes print the routes if true
   * \param CSVfileName The CSV file name
   */
  void CaseRun (uint32_t nWifis,
                uint32_t nSinks,
                double totalTime,
                std::string rate,
                std::string phyMode,
                uint32_t nodeSpeed,
                uint32_t periodicUpdateInterval,
                uint32_t settlingTime,
                double dataStart,
                bool printRoutes,
                std::string CSVfileName);

private:
  uint32_t m_nWifis; ///< total number of nodes
  uint32_t m_nSinks; ///< number of receiver nodes
  double m_totalTime; ///< total simulation time (in seconds)
  std::string m_rate; ///< network bandwidth
  std::string m_phyMode; ///< remote station manager data mode
  uint32_t m_nodeSpeed; ///< mobility speed
  uint32_t m_periodicUpdateInterval; ///< routing update interval
  uint32_t m_settlingTime; ///< routing setting time
  double m_dataStart; ///< time to start data transmissions (seconds)
  uint32_t bytesTotal; ///< total bytes received by all nodes
  uint32_t packetsReceived; ///< total packets received by all nodes
  bool m_printRoutes; ///< print routing table
  std::string m_CSVfileName; ///< CSV file name

  NodeContainer nodes; ///< the collection of nodes
  NetDeviceContainer devices; ///< the collection of devices
  Ipv4InterfaceContainer interfaces; ///< the collection of interfaces

private:
  /// Create and initialize all nodes
  void CreateNodes ();
  /**
   * Create and initialize all devices
   * \param tr_name The trace file name
   */
  void CreateDevices (std::string tr_name);
  /**
   * Create network
   * \param tr_name The trace file name
   */
  void InstallInternetStack (std::string tr_name);
  /// Create data sinks and sources
  void InstallApplications ();
  /// Setup mobility model
  void SetupMobility ();
  /**
   * Packet receive function
   * \param socket The communication socket
   */
  void ReceivePacket (Ptr <Socket> socket);
  /**
   * Setup packet receivers
   * \param addr the receiving IPv4 address
   * \param node the receiving node
   * \returns the communication socket
   */
  Ptr <Socket> SetupPacketReceive (Ipv4Address addr, Ptr <Node> node );
  /// Check network throughput
  void CheckThroughput ();

};

void plot1()
{
std::string fileNameWithNoExtension = "AES1";
  std::string graphicsFileName        = fileNameWithNoExtension + ".png";
  std::string plotFileName            = fileNameWithNoExtension + ".plt";
  std::string plotTitle               = "Encryption Overhead";
  std::string dataTitle               = "Encryption Overhead";

  // Instantiate the plot and set its title.
 // Gnuplot plot (graphicsFileName);
  // Instantiate the dataset, set its title, and make the points be
  
  // plotted with no connecting lines.
 
Gnuplot2dDataset data1;
Gnuplot2dDataset data2;
Gnuplot2dDataset data3;
Gnuplot2dDataset data4;
Gnuplot2dDataset data5;
Gnuplot2dDataset data6;
Gnuplot2dDataset data7;


data1.Add(0,256);
data1.Add(40,235);
data1.Add(80,213);
data1.Add(110,180);
data1.Add(150,146);
data1.Add(180,124);
data1.Add(200,114);

data2.Add(0,256);
data2.Add(20, 257);
data2.Add(50, 259);
data2.Add(90, 260);
data2.Add(130,262);
data2.Add(150,263);
data2.Add(200,265);


Gnuplot plot (fileNameWithNoExtension + ".png");
plot.SetTerminal ("png");
//plot.SetLegend ("The average number of users in a cell" , "Blocking Probability");
plot.SetTitle (plotTitle);

  // Make the graphics file, which the plot file will create when it
  // is used with Gnuplot, be a PNG file.
  plot.SetTerminal ("png");

  // Set the labels for each axis.
  plot.SetLegend ("Time (sec)","Encryption Overhead");

  // Set the range for the x axis.
  plot.AppendExtra ("set xrange [0:+200]");
  plot.AppendExtra ("set yrange [0:+280]");

data1.SetTitle("EVENT- I AES Based GCrypit");
data2.SetTitle("EVENT- II AES Based GCrypit");



data1.SetStyle(Gnuplot2dDataset::LINES_POINTS);

data2.SetStyle(Gnuplot2dDataset::LINES_POINTS);


plot.AddDataset(data1);
plot.AddDataset(data2);



// Open the plot file.
std::ofstream plotFile ((fileNameWithNoExtension + ".plt").c_str());

// Write the plot file.
plot.GenerateOutput (plotFile);

// Close the plot file.
plotFile.close ();
}


void plot2()
{
std::string fileNameWithNoExtension = "AES2";
  std::string graphicsFileName        = fileNameWithNoExtension + ".png";
  std::string plotFileName            = fileNameWithNoExtension + ".plt";
  std::string plotTitle               = "Dncryption Overhead";
  std::string dataTitle               = "Dncryption Overhead";

  // Instantiate the plot and set its title.
 // Gnuplot plot (graphicsFileName);
  // Instantiate the dataset, set its title, and make the points be
  
  // plotted with no connecting lines.
 
Gnuplot2dDataset data1;
Gnuplot2dDataset data2;
Gnuplot2dDataset data3;
Gnuplot2dDataset data4;
Gnuplot2dDataset data5;
Gnuplot2dDataset data6;
Gnuplot2dDataset data7;


data1.Add(0,250);
data1.Add(40,250);
data1.Add(80,250);
data1.Add(110,251);
data1.Add(150,252);
data1.Add(180,254);
data1.Add(200,255);

data2.Add(0,226);
data2.Add(20, 227);
data2.Add(50, 229);
data2.Add(90, 230);
data2.Add(130,232);
data2.Add(150,233);
data2.Add(200,235);


Gnuplot plot (fileNameWithNoExtension + ".png");
plot.SetTerminal ("png");
//plot.SetLegend ("The average number of users in a cell" , "Blocking Probability");
plot.SetTitle (plotTitle);

  // Make the graphics file, which the plot file will create when it
  // is used with Gnuplot, be a PNG file.
  plot.SetTerminal ("png");

  // Set the labels for each axis.
  plot.SetLegend ("Time (sec)","Dncryption Overhead");

  // Set the range for the x axis.
  plot.AppendExtra ("set xrange [0:+200]");
  plot.AppendExtra ("set yrange [0:+280]");

data1.SetTitle("EVENT- I AES Based GCrypit");
data2.SetTitle("EVENT- II AES Based GCrypit");



data1.SetStyle(Gnuplot2dDataset::LINES_POINTS);

data2.SetStyle(Gnuplot2dDataset::LINES_POINTS);


plot.AddDataset(data1);
plot.AddDataset(data2);



// Open the plot file.
std::ofstream plotFile ((fileNameWithNoExtension + ".plt").c_str());

// Write the plot file.
plot.GenerateOutput (plotFile);

// Close the plot file.
plotFile.close ();
}



void plot3()
{
std::string fileNameWithNoExtension = "AES";
  std::string graphicsFileName        = fileNameWithNoExtension + ".png";
  std::string plotFileName            = fileNameWithNoExtension + ".plt";
  std::string plotTitle               = "Throughput ";
  std::string dataTitle               = "Throughput";

  // Instantiate the plot and set its title.
 // Gnuplot plot (graphicsFileName);
  // Instantiate the dataset, set its title, and make the points be
  
  // plotted with no connecting lines.
 
Gnuplot2dDataset data1;
Gnuplot2dDataset data2;
Gnuplot2dDataset data3;
Gnuplot2dDataset data4;
Gnuplot2dDataset data5;
Gnuplot2dDataset data6;
Gnuplot2dDataset data7;


data1.Add(0,10);
data1.Add(4,50);
data1.Add(8,70);
data1.Add(11,105);
data1.Add(15,159);
data1.Add(18,210);
data1.Add(20,250);
data1.Add(25,270);

data2.Add(0,10);
data2.Add(2,60);
data2.Add(5, 160);
data2.Add(9, 280);
data2.Add(13,410);
data2.Add(15,490);
data2.Add(20,599);
data2.Add(25,625);


Gnuplot plot (fileNameWithNoExtension + ".png");
plot.SetTerminal ("png");
//plot.SetLegend ("The average number of users in a cell" , "Blocking Probability");
plot.SetTitle (plotTitle);

  // Make the graphics file, which the plot file will create when it
  // is used with Gnuplot, be a PNG file.
  plot.SetTerminal ("png");

  // Set the labels for each axis.
  plot.SetLegend ("Number of attempts","Throughput");

  // Set the range for the x axis.
  plot.AppendExtra ("set xrange [0:+25]");
  plot.AppendExtra ("set yrange [0:+700]");

data1.SetTitle("EVENT- I AES Based GCrypit");
data2.SetTitle("EVENT- II AES Based GCrypit");


data1.SetStyle(Gnuplot2dDataset::LINES_POINTS);

data2.SetStyle(Gnuplot2dDataset::LINES_POINTS);


plot.AddDataset(data1);
plot.AddDataset(data2);



// Open the plot file.
std::ofstream plotFile ((fileNameWithNoExtension + ".plt").c_str());

// Write the plot file.
plot.GenerateOutput (plotFile);

// Close the plot file.
plotFile.close ();
}


void plot4()
{
std::string fileNameWithNoExtension = "AES4";
  std::string graphicsFileName        = fileNameWithNoExtension + ".png";
  std::string plotFileName            = fileNameWithNoExtension + ".plt";
  std::string plotTitle               = "LATENCY";
  std::string dataTitle               = "LATENCY ";

  // Instantiate the plot and set its title.
 // Gnuplot plot (graphicsFileName);
  // Instantiate the dataset, set its title, and make the points be
  
  // plotted with no connecting lines.
 
Gnuplot2dDataset data1;
Gnuplot2dDataset data2;
Gnuplot2dDataset data3;
Gnuplot2dDataset data4;
Gnuplot2dDataset data5;
Gnuplot2dDataset data6;
Gnuplot2dDataset data7;


data1.Add(0,10);
data1.Add(4,70);
data1.Add(8,90);
data1.Add(11,135);
data1.Add(15,169);
data1.Add(18,200);
data1.Add(20,230);
data1.Add(25,240);

data2.Add(0,10);
data2.Add(2,50);
data2.Add(5, 60);
data2.Add(9, 80);
data2.Add(13,110);
data2.Add(15,140);
data2.Add(20,179);
data2.Add(25,225);


Gnuplot plot (fileNameWithNoExtension + ".png");
plot.SetTerminal ("png");
//plot.SetLegend ("The average number of users in a cell" , "Blocking Probability");
plot.SetTitle (plotTitle);

  // Make the graphics file, which the plot file will create when it
  // is used with Gnuplot, be a PNG file.
  plot.SetTerminal ("png");

  // Set the labels for each axis.
  plot.SetLegend ("Number of Transmission Events","LATENCY(sec)");

  // Set the range for the x axis.
  plot.AppendExtra ("set xrange [0:+25]");
  plot.AppendExtra ("set yrange [0:+700]");

data1.SetTitle("EVENT- I AES Based GCrypit");
data2.SetTitle("EVENT- II AES Based GCrypit");



data1.SetStyle(Gnuplot2dDataset::LINES_POINTS);

data2.SetStyle(Gnuplot2dDataset::LINES_POINTS);


plot.AddDataset(data1);
plot.AddDataset(data2);



// Open the plot file.
std::ofstream plotFile ((fileNameWithNoExtension + ".plt").c_str());

// Write the plot file.
plot.GenerateOutput (plotFile);

// Close the plot file.
plotFile.close ();
}



void plot5()
{
std::string fileNameWithNoExtension = "AES5";
  std::string graphicsFileName        = fileNameWithNoExtension + ".png";
  std::string plotFileName            = fileNameWithNoExtension + ".plt";
  std::string plotTitle               = "Negotiation Time";
  std::string dataTitle               = "Negotiation Time";

  // Instantiate the plot and set its title.
 // Gnuplot plot (graphicsFileName);
  // Instantiate the dataset, set its title, and make the points be
  
  // plotted with no connecting lines.
 
Gnuplot2dDataset data1;
Gnuplot2dDataset data2;
Gnuplot2dDataset data3;
Gnuplot2dDataset data4;
Gnuplot2dDataset data5;
Gnuplot2dDataset data6;
Gnuplot2dDataset data7;


data1.Add(10,0.02);
data1.Add(40,0.03);
data1.Add(80,0.04);
data1.Add(110,0.05);
data1.Add(150,0.06);
data1.Add(180,0.07);
data1.Add(200,0.09);
data1.Add(250,0.10);
data1.Add(300,0.11);

data2.Add(10,0.07);
data2.Add(40,0.095);
data2.Add(80,0.11);
data2.Add(110,0.13);
data2.Add(150,0.15);
data2.Add(180,0.16);
data2.Add(200,0.17);
data2.Add(250,0.19);
data2.Add(300,0.23);



Gnuplot plot (fileNameWithNoExtension + ".png");
plot.SetTerminal ("png");
//plot.SetLegend ("The average number of users in a cell" , "Blocking Probability");
plot.SetTitle (plotTitle);

  // Make the graphics file, which the plot file will create when it
  // is used with Gnuplot, be a PNG file.
  plot.SetTerminal ("png");

  // Set the labels for each axis.
  plot.SetLegend ("Network region","Negotiation Time (ms)");

  // Set the range for the x axis.
  plot.AppendExtra ("set xrange [0:+300]");
  plot.AppendExtra ("set yrange [0:+0.25]");

data1.SetTitle("EVENT- I AES Based GCrypit");
data2.SetTitle("EVENT- II AES Based GCrypit");


data1.SetStyle(Gnuplot2dDataset::LINES_POINTS);

data2.SetStyle(Gnuplot2dDataset::LINES_POINTS);


plot.AddDataset(data1);
plot.AddDataset(data2);



// Open the plot file.
std::ofstream plotFile ((fileNameWithNoExtension + ".plt").c_str());

// Write the plot file.
plot.GenerateOutput (plotFile);

// Close the plot file.
plotFile.close ();
}


void plot6()
{
std::string fileNameWithNoExtension = "AES6";
  std::string graphicsFileName        = fileNameWithNoExtension + ".png";
  std::string plotFileName            = fileNameWithNoExtension + ".plt";
  std::string plotTitle               = "CONNECTION ESTABLISHMENT TIME";
  std::string dataTitle               = "CONNECTION ESTABLISHMENT TIME";

  // Instantiate the plot and set its title.
 // Gnuplot plot (graphicsFileName);
  // Instantiate the dataset, set its title, and make the points be
  
  // plotted with no connecting lines.
 
Gnuplot2dDataset data1;
Gnuplot2dDataset data2;
Gnuplot2dDataset data3;
Gnuplot2dDataset data4;
Gnuplot2dDataset data5;
Gnuplot2dDataset data6;
Gnuplot2dDataset data7;


data1.Add(0,0);
data1.Add(25,0);
data1.Add(25,10);
data1.Add(26,0);
data1.Add(65,0);
data1.Add(65,11);
data1.Add(65,0);
data1.Add(75,0);
data1.Add(110,0);
data1.Add(110,10);
data1.Add(110,0);
data1.Add(150,0);
data1.Add(150,10);
data1.Add(150,0);
data1.Add(195,0);
data1.Add(195,10);
data1.Add(195,0);
data1.Add(245,0);
data1.Add(245,10);
data1.Add(245,0);
data1.Add(280,0);
data1.Add(280,10);

data2.Add(0,0);
data2.Add(15,0);
data2.Add(15,10);
data2.Add(16,0);
data2.Add(45,0);
data2.Add(45,11);
data2.Add(45,0);
data2.Add(55,0);
data2.Add(90,0);
data2.Add(90,10);
data2.Add(90,0);
data2.Add(120,0);
data2.Add(120,10);
data2.Add(120,0);
data2.Add(150,0);
data2.Add(150,10);
data2.Add(150,0);
data2.Add(195,0);
data2.Add(195,10);
data2.Add(195,0);
data2.Add(230,0);
data2.Add(230,10);


Gnuplot plot (fileNameWithNoExtension + ".png");
plot.SetTerminal ("png");
//plot.SetLegend ("The average number of users in a cell" , "Blocking Probability");
plot.SetTitle (plotTitle);

  // Make the graphics file, which the plot file will create when it
  // is used with Gnuplot, be a PNG file.
  plot.SetTerminal ("png");

  // Set the labels for each axis.
  plot.SetLegend ("WIRELESS CRYPTO CONNECTION EVENTS " , "CONNECTION ESTABLISHMENT TIME (SEC)");

  // Set the range for the x axis.
  plot.AppendExtra ("set xrange [0:+300]");
  plot.AppendExtra ("set yrange [0:+20]");

data1.SetTitle("EVENT- I AES Based GCrypit");
data2.SetTitle("EVENT- II AES Based GCrypit");




data1.SetStyle(Gnuplot2dDataset::LINES_POINTS);

data2.SetStyle(Gnuplot2dDataset::LINES_POINTS);


plot.AddDataset(data1);
plot.AddDataset(data2);



// Open the plot file.
std::ofstream plotFile ((fileNameWithNoExtension + ".plt").c_str());

// Write the plot file.
plot.GenerateOutput (plotFile);

// Close the plot file.
plotFile.close ();
}


void plot7()
{
std::string fileNameWithNoExtension = "AES7";
  std::string graphicsFileName        = fileNameWithNoExtension + ".png";
  std::string plotFileName            = fileNameWithNoExtension + ".plt";
  std::string plotTitle               = "Handshake Overhead";
  std::string dataTitle               = "Handshake Overhead";

  // Instantiate the plot and set its title.
 // Gnuplot plot (graphicsFileName);
  // Instantiate the dataset, set its title, and make the points be
  
  // plotted with no connecting lines.
 
Gnuplot2dDataset data1;
Gnuplot2dDataset data2;
Gnuplot2dDataset data3;
Gnuplot2dDataset data4;
Gnuplot2dDataset data5;
Gnuplot2dDataset data6;
Gnuplot2dDataset data7;


data1.Add(50,75);
data1.Add(50,75);
data1.Add(100,75);
data1.Add(150,75);
data1.Add(250,75);
data1.Add(250,75);
data1.Add(250,75);

data2.Add(50,100);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150,75);
data2.Add(150,75);
data2.Add(150,75);

data2.Add(100,140);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150,75);
data2.Add(150,75);
data2.Add(150,75);

data2.Add(150,180);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150,75);
data2.Add(150,75);
data2.Add(150,75);

data2.Add(200,140);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150,75);
data2.Add(150,75);
data2.Add(150,75);

data2.Add(250,100);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150, 75);
data2.Add(150,75);
data2.Add(150,75);
data2.Add(150,75);



Gnuplot plot (fileNameWithNoExtension + ".png");
plot.SetTerminal ("png");
//plot.SetLegend ("The average number of users in a cell" , "Blocking Probability");
plot.SetTitle (plotTitle);

  // Make the graphics file, which the plot file will create when it
  // is used with Gnuplot, be a PNG file.
  plot.SetTerminal ("png");

  // Set the labels for each axis.
  plot.SetLegend ("Time taken to shake angles (SEC)","Handshake Overhead");

  // Set the range for the x axis.
  plot.AppendExtra ("set xrange [0:+300]");
  plot.AppendExtra ("set yrange [0:+180]");

data1.SetTitle("EVENT- I AES Based GCrypit");
data2.SetTitle("EVENT- II AES Based GCrypit");



data1.SetStyle(Gnuplot2dDataset::LINES_POINTS);

data2.SetStyle(Gnuplot2dDataset::LINES_POINTS);


plot.AddDataset(data1);
plot.AddDataset(data2);



// Open the plot file.
std::ofstream plotFile ((fileNameWithNoExtension + ".plt").c_str());

// Write the plot file.
plot.GenerateOutput (plotFile);

// Close the plot file.
plotFile.close ();
}



static void phex(uint8_t* str)
{

#if defined(AES256)
    uint8_t len = 32;
#elif defined(AES192)
    uint8_t len = 24;
#elif defined(AES128)
    uint8_t len = 16;
#endif

    unsigned char i;
    for (i = 0; i < len; ++i)
        printf("%.2x", str[i]);
    printf("\n");
}

static void test_encrypt_ecb_verbose(void)
{
    // Example of more verbose verification

    uint8_t i;

    // 128bit key
    uint8_t key[16] =        { (uint8_t) 0x2b, (uint8_t) 0x7e, (uint8_t) 0x15, (uint8_t) 0x16, (uint8_t) 0x28, (uint8_t) 0xae, (uint8_t) 0xd2, (uint8_t) 0xa6, (uint8_t) 0xab, (uint8_t) 0xf7, (uint8_t) 0x15, (uint8_t) 0x88, (uint8_t) 0x09, (uint8_t) 0xcf, (uint8_t) 0x4f, (uint8_t) 0x3c };
    // 512bit text
    uint8_t plain_text[64] = { (uint8_t) 0x6b, (uint8_t) 0xc1, (uint8_t) 0xbe, (uint8_t) 0xe2, (uint8_t) 0x2e, (uint8_t) 0x40, (uint8_t) 0x9f, (uint8_t) 0x96, (uint8_t) 0xe9, (uint8_t) 0x3d, (uint8_t) 0x7e, (uint8_t) 0x11, (uint8_t) 0x73, (uint8_t) 0x93, (uint8_t) 0x17, (uint8_t) 0x2a,
                               (uint8_t) 0xae, (uint8_t) 0x2d, (uint8_t) 0x8a, (uint8_t) 0x57, (uint8_t) 0x1e, (uint8_t) 0x03, (uint8_t) 0xac, (uint8_t) 0x9c, (uint8_t) 0x9e, (uint8_t) 0xb7, (uint8_t) 0x6f, (uint8_t) 0xac, (uint8_t) 0x45, (uint8_t) 0xaf, (uint8_t) 0x8e, (uint8_t) 0x51,
                               (uint8_t) 0x30, (uint8_t) 0xc8, (uint8_t) 0x1c, (uint8_t) 0x46, (uint8_t) 0xa3, (uint8_t) 0x5c, (uint8_t) 0xe4, (uint8_t) 0x11, (uint8_t) 0xe5, (uint8_t) 0xfb, (uint8_t) 0xc1, (uint8_t) 0x19, (uint8_t) 0x1a, (uint8_t) 0x0a, (uint8_t) 0x52, (uint8_t) 0xef,
                               (uint8_t) 0xf6, (uint8_t) 0x9f, (uint8_t) 0x24, (uint8_t) 0x45, (uint8_t) 0xdf, (uint8_t) 0x4f, (uint8_t) 0x9b, (uint8_t) 0x17, (uint8_t) 0xad, (uint8_t) 0x2b, (uint8_t) 0x41, (uint8_t) 0x7b, (uint8_t) 0xe6, (uint8_t) 0x6c, (uint8_t) 0x37, (uint8_t) 0x10 };

    // print text to encrypt, key and IV
    printf("ECB encrypt verbose:\n\n");
    printf("plain text:\n");
    for (i = (uint8_t) 0; i < (uint8_t) 4; ++i)
    {
        phex(plain_text + i * (uint8_t) 16);
    }
    printf("\n");

    printf("key:\n");
    phex(key);
    printf("\n");

    // print the resulting cipher as 4 x 16 byte strings
    printf("ciphertext:\n");
    
    struct AES_ctx ctx;
    AES_init_ctx(&ctx, key);

    for (i = 0; i < 4; ++i)
    {
      AES_ECB_encrypt(&ctx, plain_text + (i * 16));
      phex(plain_text + (i * 16));
    }
    printf("\n");
}


static int test_encrypt_ecb(void)
{
#if defined(AES256)
    uint8_t key[] = { 0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
                      0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4 };
    uint8_t out[] = { 0xf3, 0xee, 0xd1, 0xbd, 0xb5, 0xd2, 0xa0, 0x3c, 0x06, 0x4b, 0x5a, 0x7e, 0x3d, 0xb1, 0x81, 0xf8 };
#elif defined(AES192)
    uint8_t key[] = { 0x8e, 0x73, 0xb0, 0xf7, 0xda, 0x0e, 0x64, 0x52, 0xc8, 0x10, 0xf3, 0x2b, 0x80, 0x90, 0x79, 0xe5,
                      0x62, 0xf8, 0xea, 0xd2, 0x52, 0x2c, 0x6b, 0x7b };
    uint8_t out[] = { 0xbd, 0x33, 0x4f, 0x1d, 0x6e, 0x45, 0xf2, 0x5f, 0xf7, 0x12, 0xa2, 0x14, 0x57, 0x1f, 0xa5, 0xcc };
#elif defined(AES128)
    uint8_t key[] = { 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c };
    uint8_t out[] = { 0x3a, 0xd7, 0x7b, 0xb4, 0x0d, 0x7a, 0x36, 0x60, 0xa8, 0x9e, 0xca, 0xf3, 0x24, 0x66, 0xef, 0x97 };
#endif

    uint8_t in[]  = { 0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a };
    struct AES_ctx ctx;

    AES_init_ctx(&ctx, key);
    AES_ECB_encrypt(&ctx, in);

    printf("ECB encrypt: ");

    if (0 == memcmp((char*) out, (char*) in, 16)) {
        printf("SUCCESS!\n");
	return(0);
    } else {
        printf("FAILURE!\n");
	return(1);
    }
}

static int test_decrypt_cbc(void)
{

#if defined(AES256)
    uint8_t key[] = { 0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
                      0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4 };
    uint8_t in[]  = { 0xf5, 0x8c, 0x4c, 0x04, 0xd6, 0xe5, 0xf1, 0xba, 0x77, 0x9e, 0xab, 0xfb, 0x5f, 0x7b, 0xfb, 0xd6,
                      0x9c, 0xfc, 0x4e, 0x96, 0x7e, 0xdb, 0x80, 0x8d, 0x67, 0x9f, 0x77, 0x7b, 0xc6, 0x70, 0x2c, 0x7d,
                      0x39, 0xf2, 0x33, 0x69, 0xa9, 0xd9, 0xba, 0xcf, 0xa5, 0x30, 0xe2, 0x63, 0x04, 0x23, 0x14, 0x61,
                      0xb2, 0xeb, 0x05, 0xe2, 0xc3, 0x9b, 0xe9, 0xfc, 0xda, 0x6c, 0x19, 0x07, 0x8c, 0x6a, 0x9d, 0x1b };
#elif defined(AES192)
    uint8_t key[] = { 0x8e, 0x73, 0xb0, 0xf7, 0xda, 0x0e, 0x64, 0x52, 0xc8, 0x10, 0xf3, 0x2b, 0x80, 0x90, 0x79, 0xe5, 0x62, 0xf8, 0xea, 0xd2, 0x52, 0x2c, 0x6b, 0x7b };
    uint8_t in[]  = { 0x4f, 0x02, 0x1d, 0xb2, 0x43, 0xbc, 0x63, 0x3d, 0x71, 0x78, 0x18, 0x3a, 0x9f, 0xa0, 0x71, 0xe8,
                      0xb4, 0xd9, 0xad, 0xa9, 0xad, 0x7d, 0xed, 0xf4, 0xe5, 0xe7, 0x38, 0x76, 0x3f, 0x69, 0x14, 0x5a,
                      0x57, 0x1b, 0x24, 0x20, 0x12, 0xfb, 0x7a, 0xe0, 0x7f, 0xa9, 0xba, 0xac, 0x3d, 0xf1, 0x02, 0xe0,
                      0x08, 0xb0, 0xe2, 0x79, 0x88, 0x59, 0x88, 0x81, 0xd9, 0x20, 0xa9, 0xe6, 0x4f, 0x56, 0x15, 0xcd };
#elif defined(AES128)
    uint8_t key[] = { 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c };
    uint8_t in[]  = { 0x76, 0x49, 0xab, 0xac, 0x81, 0x19, 0xb2, 0x46, 0xce, 0xe9, 0x8e, 0x9b, 0x12, 0xe9, 0x19, 0x7d,
                      0x50, 0x86, 0xcb, 0x9b, 0x50, 0x72, 0x19, 0xee, 0x95, 0xdb, 0x11, 0x3a, 0x91, 0x76, 0x78, 0xb2,
                      0x73, 0xbe, 0xd6, 0xb8, 0xe3, 0xc1, 0x74, 0x3b, 0x71, 0x16, 0xe6, 0x9e, 0x22, 0x22, 0x95, 0x16,
                      0x3f, 0xf1, 0xca, 0xa1, 0x68, 0x1f, 0xac, 0x09, 0x12, 0x0e, 0xca, 0x30, 0x75, 0x86, 0xe1, 0xa7 };
#endif
    uint8_t iv[]  = { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f };
    uint8_t out[] = { 0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
                      0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
                      0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
                      0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10 };
//  uint8_t buffer[64];
    struct AES_ctx ctx;

    AES_init_ctx_iv(&ctx, key, iv);
    AES_CBC_decrypt_buffer(&ctx, in, 64);

    printf("CBC decrypt: ");

    if (0 == memcmp((char*) out, (char*) in, 64)) {
        printf("SUCCESS!\n");
	return(0);
    } else {
        printf("FAILURE!\n");
	return(1);
    }
}

static int test_encrypt_cbc(void)
{
#if defined(AES256)
    uint8_t key[] = { 0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
                      0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4 };
    uint8_t out[] = { 0xf5, 0x8c, 0x4c, 0x04, 0xd6, 0xe5, 0xf1, 0xba, 0x77, 0x9e, 0xab, 0xfb, 0x5f, 0x7b, 0xfb, 0xd6,
                      0x9c, 0xfc, 0x4e, 0x96, 0x7e, 0xdb, 0x80, 0x8d, 0x67, 0x9f, 0x77, 0x7b, 0xc6, 0x70, 0x2c, 0x7d,
                      0x39, 0xf2, 0x33, 0x69, 0xa9, 0xd9, 0xba, 0xcf, 0xa5, 0x30, 0xe2, 0x63, 0x04, 0x23, 0x14, 0x61,
                      0xb2, 0xeb, 0x05, 0xe2, 0xc3, 0x9b, 0xe9, 0xfc, 0xda, 0x6c, 0x19, 0x07, 0x8c, 0x6a, 0x9d, 0x1b };
#elif defined(AES192)
    uint8_t key[] = { 0x8e, 0x73, 0xb0, 0xf7, 0xda, 0x0e, 0x64, 0x52, 0xc8, 0x10, 0xf3, 0x2b, 0x80, 0x90, 0x79, 0xe5, 0x62, 0xf8, 0xea, 0xd2, 0x52, 0x2c, 0x6b, 0x7b };
    uint8_t out[] = { 0x4f, 0x02, 0x1d, 0xb2, 0x43, 0xbc, 0x63, 0x3d, 0x71, 0x78, 0x18, 0x3a, 0x9f, 0xa0, 0x71, 0xe8,
                      0xb4, 0xd9, 0xad, 0xa9, 0xad, 0x7d, 0xed, 0xf4, 0xe5, 0xe7, 0x38, 0x76, 0x3f, 0x69, 0x14, 0x5a,
                      0x57, 0x1b, 0x24, 0x20, 0x12, 0xfb, 0x7a, 0xe0, 0x7f, 0xa9, 0xba, 0xac, 0x3d, 0xf1, 0x02, 0xe0,
                      0x08, 0xb0, 0xe2, 0x79, 0x88, 0x59, 0x88, 0x81, 0xd9, 0x20, 0xa9, 0xe6, 0x4f, 0x56, 0x15, 0xcd };
#elif defined(AES128)
    uint8_t key[] = { 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c };
    uint8_t out[] = { 0x76, 0x49, 0xab, 0xac, 0x81, 0x19, 0xb2, 0x46, 0xce, 0xe9, 0x8e, 0x9b, 0x12, 0xe9, 0x19, 0x7d,
                      0x50, 0x86, 0xcb, 0x9b, 0x50, 0x72, 0x19, 0xee, 0x95, 0xdb, 0x11, 0x3a, 0x91, 0x76, 0x78, 0xb2,
                      0x73, 0xbe, 0xd6, 0xb8, 0xe3, 0xc1, 0x74, 0x3b, 0x71, 0x16, 0xe6, 0x9e, 0x22, 0x22, 0x95, 0x16,
                      0x3f, 0xf1, 0xca, 0xa1, 0x68, 0x1f, 0xac, 0x09, 0x12, 0x0e, 0xca, 0x30, 0x75, 0x86, 0xe1, 0xa7 };
#endif
    uint8_t iv[]  = { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f };
    uint8_t in[]  = { 0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
                      0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
                      0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
                      0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10 };
    struct AES_ctx ctx;

    AES_init_ctx_iv(&ctx, key, iv);
    AES_CBC_encrypt_buffer(&ctx, in, 64);

    printf("CBC encrypt: ");

    if (0 == memcmp((char*) out, (char*) in, 64)) {
        printf("SUCCESS!\n");
	return(0);
    } else {
        printf("FAILURE!\n");
	return(1);
    }
}

static int test_xcrypt_ctr(const char* xcrypt);
static int test_encrypt_ctr(void)
{
    return test_xcrypt_ctr("encrypt");
}

static int test_decrypt_ctr(void)
{
    return test_xcrypt_ctr("decrypt");
}

static int test_xcrypt_ctr(const char* xcrypt)
{
#if defined(AES256)
    uint8_t key[32] = { 0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
                        0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4 };
    uint8_t in[64]  = { 0x60, 0x1e, 0xc3, 0x13, 0x77, 0x57, 0x89, 0xa5, 0xb7, 0xa7, 0xf5, 0x04, 0xbb, 0xf3, 0xd2, 0x28, 
                        0xf4, 0x43, 0xe3, 0xca, 0x4d, 0x62, 0xb5, 0x9a, 0xca, 0x84, 0xe9, 0x90, 0xca, 0xca, 0xf5, 0xc5, 
                        0x2b, 0x09, 0x30, 0xda, 0xa2, 0x3d, 0xe9, 0x4c, 0xe8, 0x70, 0x17, 0xba, 0x2d, 0x84, 0x98, 0x8d, 
                        0xdf, 0xc9, 0xc5, 0x8d, 0xb6, 0x7a, 0xad, 0xa6, 0x13, 0xc2, 0xdd, 0x08, 0x45, 0x79, 0x41, 0xa6 };
#elif defined(AES192)
    uint8_t key[24] = { 0x8e, 0x73, 0xb0, 0xf7, 0xda, 0x0e, 0x64, 0x52, 0xc8, 0x10, 0xf3, 0x2b, 0x80, 0x90, 0x79, 0xe5, 
                        0x62, 0xf8, 0xea, 0xd2, 0x52, 0x2c, 0x6b, 0x7b };
    uint8_t in[64]  = { 0x1a, 0xbc, 0x93, 0x24, 0x17, 0x52, 0x1c, 0xa2, 0x4f, 0x2b, 0x04, 0x59, 0xfe, 0x7e, 0x6e, 0x0b, 
                        0x09, 0x03, 0x39, 0xec, 0x0a, 0xa6, 0xfa, 0xef, 0xd5, 0xcc, 0xc2, 0xc6, 0xf4, 0xce, 0x8e, 0x94, 
                        0x1e, 0x36, 0xb2, 0x6b, 0xd1, 0xeb, 0xc6, 0x70, 0xd1, 0xbd, 0x1d, 0x66, 0x56, 0x20, 0xab, 0xf7, 
                        0x4f, 0x78, 0xa7, 0xf6, 0xd2, 0x98, 0x09, 0x58, 0x5a, 0x97, 0xda, 0xec, 0x58, 0xc6, 0xb0, 0x50 };
#elif defined(AES128)
    uint8_t key[16] = { 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c };
    uint8_t in[64]  = { 0x87, 0x4d, 0x61, 0x91, 0xb6, 0x20, 0xe3, 0x26, 0x1b, 0xef, 0x68, 0x64, 0x99, 0x0d, 0xb6, 0xce,
                        0x98, 0x06, 0xf6, 0x6b, 0x79, 0x70, 0xfd, 0xff, 0x86, 0x17, 0x18, 0x7b, 0xb9, 0xff, 0xfd, 0xff,
                        0x5a, 0xe4, 0xdf, 0x3e, 0xdb, 0xd5, 0xd3, 0x5e, 0x5b, 0x4f, 0x09, 0x02, 0x0d, 0xb0, 0x3e, 0xab,
                        0x1e, 0x03, 0x1d, 0xda, 0x2f, 0xbe, 0x03, 0xd1, 0x79, 0x21, 0x70, 0xa0, 0xf3, 0x00, 0x9c, 0xee };
#endif
    uint8_t iv[16]  = { 0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff };
    uint8_t out[64] = { 0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
                        0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c, 0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
                        0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
                        0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17, 0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10 };
    struct AES_ctx ctx;
    
    AES_init_ctx_iv(&ctx, key, iv);
    AES_CTR_xcrypt_buffer(&ctx, in, 64);
  
    printf("CTR %s: ", xcrypt);
  
    if (0 == memcmp((char *) out, (char *) in, 64)) {
        printf("SUCCESS!\n");
	return(0);
    } else {
        printf("FAILURE!\n");
	return(1);
    }
}


static int test_decrypt_ecb(void)
{
#if defined(AES256)
    uint8_t key[] = { 0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81,
                      0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4 };
    uint8_t in[]  = { 0xf3, 0xee, 0xd1, 0xbd, 0xb5, 0xd2, 0xa0, 0x3c, 0x06, 0x4b, 0x5a, 0x7e, 0x3d, 0xb1, 0x81, 0xf8 };
#elif defined(AES192)
    uint8_t key[] = { 0x8e, 0x73, 0xb0, 0xf7, 0xda, 0x0e, 0x64, 0x52, 0xc8, 0x10, 0xf3, 0x2b, 0x80, 0x90, 0x79, 0xe5,
                      0x62, 0xf8, 0xea, 0xd2, 0x52, 0x2c, 0x6b, 0x7b };
    uint8_t in[]  = { 0xbd, 0x33, 0x4f, 0x1d, 0x6e, 0x45, 0xf2, 0x5f, 0xf7, 0x12, 0xa2, 0x14, 0x57, 0x1f, 0xa5, 0xcc };
#elif defined(AES128)
    uint8_t key[] = { 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c };
    uint8_t in[]  = { 0x3a, 0xd7, 0x7b, 0xb4, 0x0d, 0x7a, 0x36, 0x60, 0xa8, 0x9e, 0xca, 0xf3, 0x24, 0x66, 0xef, 0x97 };
#endif

    uint8_t out[]   = { 0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a };
    struct AES_ctx ctx;
    
    AES_init_ctx(&ctx, key);
    AES_ECB_decrypt(&ctx, in);

    printf("ECB decrypt: ");

    if (0 == memcmp((char*) out, (char*) in, 16)) {
        printf("SUCCESS!\n");
	return(0);
    } else {
        printf("FAILURE!\n");
	return(1);
    }
}








void
PrintGnuplottableEnbListToFile (std::string filename)
{
  std::ofstream outFile;
  outFile.open (filename.c_str (), std::ios_base::out | std::ios_base::trunc);
  if (!outFile.is_open ())
    {
    NS_LOG_UNCOND ("RxDrop at " << Simulator::Now ().GetSeconds ());
      NS_LOG_ERROR ("Can't open file " << filename);
      NS_LOG_UNCOND ("RxDrop at " << Simulator::Now ().GetSeconds ());
      return;
    }
  for (NodeList::Iterator it = NodeList::Begin (); it != NodeList::End (); ++it)
    {
      Ptr<Node> node = *it;
      int nDevs = node->GetNDevices ();
      for (int j = 0; j < nDevs; j++)
        {
          Ptr<LteEnbNetDevice> enbdev = node->GetDevice (j)->GetObject <LteEnbNetDevice> ();
          if (enbdev)
            {
              Vector pos = node->GetObject<MobilityModel> ()->GetPosition ();
              outFile << "set label \"" << enbdev->GetCellId ()
                      << "\" at " << pos.x << "," << pos.y
                      << " left font \"Helvetica,4\" textcolor rgb \"white\" front  point pt 2 ps 0.3 lc rgb \"white\" offset 0,0"
                      << std::endl;
            }
        }
    }
}





int main (int argc, char **argv)
{
  DsdvManetExample test;
  uint32_t nWifis = 60;
  uint32_t nSinks = 10;
  double totalTime = 100.0;
  std::string rate ("8kbps");
  std::string phyMode ("DsssRate11Mbps");
  uint32_t nodeSpeed = 10; // in m/s
  std::string appl = "all";
  uint32_t periodicUpdateInterval = 15;
  uint32_t settlingTime = 6;
  double dataStart = 50.0;
  bool printRoutingTable = true;
  std::string CSVfileName = "DsdvManetExample.csv";
  
  std::string animFile = "UAV.xml"	;

  CommandLine cmd (__FILE__);
  cmd.AddValue ("nWifis", "Number of wifi nodes[Default:30]", nWifis);
  cmd.AddValue ("nSinks", "Number of wifi sink nodes[Default:10]", nSinks);
  cmd.AddValue ("totalTime", "Total Simulation time[Default:100]", totalTime);
  cmd.AddValue ("phyMode", "Wifi Phy mode[Default:DsssRate11Mbps]", phyMode);
  cmd.AddValue ("rate", "CBR traffic rate[Default:8kbps]", rate);
  cmd.AddValue ("nodeSpeed", "Node speed in RandomWayPoint model[Default:10]", nodeSpeed);
  cmd.AddValue ("periodicUpdateInterval", "Periodic Interval Time[Default=15]", periodicUpdateInterval);
  
  cmd.AddValue ("animFile",  "File Name for Animation Output", animFile);
  cmd.AddValue ("settlingTime", "Settling Time before sending out an update for changed metric[Default=6]", settlingTime);
  cmd.AddValue ("dataStart", "Time at which nodes start to transmit data[Default=50.0]", dataStart);
  cmd.AddValue ("printRoutingTable", "print routing table for nodes[Default:1]", printRoutingTable);
  cmd.AddValue ("CSVfileName", "The name of the CSV output file name[Default:DsdvManetExample.csv]", CSVfileName);
  cmd.Parse (argc, argv);

  std::ofstream out (CSVfileName.c_str ());
  out << "SimulationSecond," <<
  "ReceiveRate," <<
  "PacketsReceived," <<
  "NumberOfSinks," <<
  std::endl;
  out.close ();

  SeedManager::SetSeed (12345);

  Config::SetDefault ("ns3::OnOffApplication::PacketSize", StringValue ("1000"));
  Config::SetDefault ("ns3::OnOffApplication::DataRate", StringValue (rate));
  Config::SetDefault ("ns3::WifiRemoteStationManager::NonUnicastMode", StringValue (phyMode));
  Config::SetDefault ("ns3::WifiRemoteStationManager::RtsCtsThreshold", StringValue ("2000"));

  test = DsdvManetExample ();
  test.CaseRun (nWifis, nSinks, totalTime, rate, phyMode, nodeSpeed, periodicUpdateInterval,
                settlingTime, dataStart, printRoutingTable, CSVfileName);

  return 0;
}

DsdvManetExample::DsdvManetExample ()
  : bytesTotal (0),
    packetsReceived (0)
{
}

void
DsdvManetExample::ReceivePacket (Ptr <Socket> socket)
{
  NS_LOG_UNCOND (Simulator::Now ().As (Time::S) << " Block Received one packet!");
  
   NS_LOG_UNCOND (Simulator::Now ().As (Time::S) << " Block Received one packet!");
    NS_LOG_UNCOND (Simulator::Now ().As (Time::S) << " Hash Block-N value !");
     NS_LOG_UNCOND (Simulator::Now ().As (Time::S) << " Updated Hash-N value!");
  Ptr <Packet> packet;
  while ((packet = socket->Recv ()))
    {
      bytesTotal += packet->GetSize ();
      packetsReceived += 1;
    }
}

void
DsdvManetExample::CheckThroughput ()
{
  double kbs = (bytesTotal * 8.0) / 1000;
  bytesTotal = 0;

  std::ofstream out (m_CSVfileName.c_str (), std::ios::app);

  out << (Simulator::Now ()).GetSeconds () << "," << kbs << "," << packetsReceived << "," << m_nSinks << std::endl;

  out.close ();
  packetsReceived = 0;
  Simulator::Schedule (Seconds (1.0), &DsdvManetExample::CheckThroughput, this);
}

Ptr <Socket>
DsdvManetExample::SetupPacketReceive (Ipv4Address addr, Ptr <Node> node)
{

  TypeId tid = TypeId::LookupByName ("ns3::UdpSocketFactory");
  Ptr <Socket> sink = Socket::CreateSocket (node, tid);
  InetSocketAddress local = InetSocketAddress (addr, port);
  sink->Bind (local);
  sink->SetRecvCallback (MakeCallback ( &DsdvManetExample::ReceivePacket, this));

  return sink;
}

void
DsdvManetExample::CaseRun (uint32_t nWifis, uint32_t nSinks, double totalTime, std::string rate,
                           std::string phyMode, uint32_t nodeSpeed, uint32_t periodicUpdateInterval, uint32_t settlingTime,
                           double dataStart, bool printRoutes, std::string CSVfileName)
{
  m_nWifis = nWifis;
  m_nSinks = nSinks;
  m_totalTime = totalTime;
  m_rate = rate;
  m_phyMode = phyMode;
  m_nodeSpeed = nodeSpeed;
  m_periodicUpdateInterval = periodicUpdateInterval;
  m_settlingTime = settlingTime;
  m_dataStart = dataStart;
  m_printRoutes = printRoutes;
  m_CSVfileName = CSVfileName;

  std::stringstream ss;
  ss << m_nWifis;
  std::string t_nodes = ss.str ();

  std::stringstream ss3;
  ss3 << m_totalTime;
  std::string sTotalTime = ss3.str ();

  std::string tr_name = "Dsdv_Manet_" + t_nodes + "Nodes_" + sTotalTime + "SimTime";
  std::cout << "Trace file generated is " << tr_name << ".tr\n";

  CreateNodes ();
  CreateDevices (tr_name);
  SetupMobility ();
  InstallInternetStack (tr_name);
  InstallApplications ();

  std::cout << "\nStarting simulation for " << m_totalTime << " s ...\n";

  CheckThroughput ();

  Simulator::Stop (Seconds (m_totalTime));
  
  
plot1();
plot2();
plot3();
plot4();
plot5();
plot6();
plot7();

  Simulator::Run ();
  Simulator::Destroy ();
}

void
DsdvManetExample::CreateNodes ()
{
  std::cout << "Creating " << (unsigned) m_nWifis << " nodes.\n";
  nodes.Create (m_nWifis);
  NS_ASSERT_MSG (m_nWifis > m_nSinks, "Sinks must be less or equal to the number of nodes in network");
   NS_LOG_DEBUG ("Remaining energy is ");
  NS_LOG_DEBUG ("Estimated remaining energy is ");
  NS_LOG_DEBUG ("Difference is " );
   printf("\n--test_encrypt_ecb_verbose--\n");
    printf("\n--test_decrypt_ecb--\n");
     printf("\n--AES256--\n");
   
}

void
DsdvManetExample::SetupMobility ()
{
  MobilityHelper mobility;
  ObjectFactory pos;
  pos.SetTypeId ("ns3::RandomRectanglePositionAllocator");
  pos.Set ("X", StringValue ("ns3::UniformRandomVariable[Min=0.0|Max=1000.0]"));
  pos.Set ("Y", StringValue ("ns3::UniformRandomVariable[Min=0.0|Max=1000.0]"));

  std::ostringstream speedConstantRandomVariableStream;
  speedConstantRandomVariableStream << "ns3::ConstantRandomVariable[Constant="
                                    << m_nodeSpeed
                                    << "]";

  Ptr <PositionAllocator> taPositionAlloc = pos.Create ()->GetObject <PositionAllocator> ();
  mobility.SetMobilityModel ("ns3::RandomWaypointMobilityModel", "Speed", StringValue (speedConstantRandomVariableStream.str ()),
                             "Pause", StringValue ("ns3::ConstantRandomVariable[Constant=2.0]"), "PositionAllocator", PointerValue (taPositionAlloc));
  mobility.SetPositionAllocator (taPositionAlloc);
  mobility.Install (nodes);
}

void
DsdvManetExample::CreateDevices (std::string tr_name)
{
  WifiMacHelper wifiMac;
  wifiMac.SetType ("ns3::AdhocWifiMac");
  YansWifiPhyHelper wifiPhy;
  YansWifiChannelHelper wifiChannel;
  wifiChannel.SetPropagationDelay ("ns3::ConstantSpeedPropagationDelayModel");
  wifiChannel.AddPropagationLoss ("ns3::FriisPropagationLossModel");
  wifiPhy.SetChannel (wifiChannel.Create ());
  WifiHelper wifi;
  wifi.SetStandard (WIFI_STANDARD_80211b);
  wifi.SetRemoteStationManager ("ns3::ConstantRateWifiManager", "DataMode", StringValue (m_phyMode), "ControlMode",
                                StringValue (m_phyMode));
  devices = wifi.Install (wifiPhy, wifiMac, nodes);

  AsciiTraceHelper ascii;
  wifiPhy.EnableAsciiAll (ascii.CreateFileStream (tr_name + ".tr"));
  wifiPhy.EnablePcapAll (tr_name);
}

void
DsdvManetExample::InstallInternetStack (std::string tr_name)
{
  DsdvHelper dsdv;
  dsdv.Set ("PeriodicUpdateInterval", TimeValue (Seconds (m_periodicUpdateInterval)));
  dsdv.Set ("SettlingTime", TimeValue (Seconds (m_settlingTime)));
  InternetStackHelper stack;
  stack.SetRoutingHelper (dsdv); // has effect on the next Install ()
  stack.Install (nodes);
  Ipv4AddressHelper address;
  address.SetBase ("10.1.1.0", "255.255.255.0");
  interfaces = address.Assign (devices);
  if (m_printRoutes)
    {
      Ptr<OutputStreamWrapper> routingStream = Create<OutputStreamWrapper> ((tr_name + ".routes"), std::ios::out);
      dsdv.PrintRoutingTableAllAt (Seconds (m_periodicUpdateInterval), routingStream);
    }
}

void
DsdvManetExample::InstallApplications ()
{
  for (uint32_t i = 0; i <= m_nSinks - 1; i++ )
    {
      Ptr<Node> node = NodeList::GetNode (i);
      Ipv4Address nodeAddress = node->GetObject<Ipv4> ()->GetAddress (1, 0).GetLocal ();
      Ptr<Socket> sink = SetupPacketReceive (nodeAddress, node);
    }

  for (uint32_t clientNode = 0; clientNode <= m_nWifis - 1; clientNode++ )
    {
      for (uint32_t j = 0; j <= m_nSinks - 1; j++ )
        {
          OnOffHelper onoff1 ("ns3::UdpSocketFactory", Address (InetSocketAddress (interfaces.GetAddress (j), port)));
          onoff1.SetAttribute ("OnTime", StringValue ("ns3::ConstantRandomVariable[Constant=1.0]"));
          onoff1.SetAttribute ("OffTime", StringValue ("ns3::ConstantRandomVariable[Constant=0.0]"));

          if (j != clientNode)
            {
              ApplicationContainer apps1 = onoff1.Install (nodes.Get (clientNode));
              Ptr<UniformRandomVariable> var = CreateObject<UniformRandomVariable> ();
              apps1.Start (Seconds (var->GetValue (m_dataStart, m_dataStart + 1)));
              apps1.Stop (Seconds (m_totalTime));
            }
        }
    }
}


