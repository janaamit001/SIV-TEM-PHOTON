#ifdef _MSC_VER
#define _CRT_SECURE_NO_WARNINGS
#endif

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>

#include "crypto_aead.h"
#include "photon.h"
#include "api.h"

#define KAT_SUCCESS          0
#define KAT_FILE_OPEN_ERROR -1
#define KAT_DATA_ERROR      -3
#define KAT_CRYPTO_FAILURE  -4

#define MAX_FILE_NAME				256
#define MAX_MESSAGE_LENGTH			32
#define MAX_ASSOCIATED_DATA_LENGTH	32
#define sboxSize 16
#define number 3

typedef uint8_t byte;

#define S1				4
const byte ReductionPoly1 = 0x3;
const byte WORDFILTER1 = ((byte) 1<<S1)-1;

//const unsigned char WORDFILTER = 0xF;

extern uint8_t st[8][8], st1[8][8], st2[8][8], st3[8][8], st4[8][8], st5[8][8];
extern unsigned char ftag[ 32 ], nfstate[32], fstate[32];
unsigned char tag1[32];
unsigned char s[16] = {0xc, 5, 6, 0xb, 9, 0, 0xa, 0xd, 3, 0xe, 0xf, 8, 4, 7, 1, 2};

unsigned int gl_count = 0;

const byte MixColMatrix1[D][D] = {
	{ 2,  4,  2, 11,  2,  8,  5,  6},
	{12,  9,  8, 13,  7,  7,  5,  2},
	{ 4,  4, 13, 13,  9,  4, 13,  9},
	{ 1,  6,  5,  1, 12, 13, 15, 14},
	{15, 12,  9, 13, 14,  5, 14, 13},
	{ 9, 14,  5, 15,  4, 12,  9,  6},
	{12,  2,  2, 10,  3,  1,  1, 14},
	{15,  1, 13, 10,  5, 10,  2,  3}
};


const byte invMixColMatrix[D][D] = {
				{4, 7, 9, 10, 12, 12, 3, 15},
				{13, 13, 10, 10, 7, 13, 10, 7},
				{14, 2, 3, 14, 4, 10, 5, 11},
				{5, 4, 7, 10, 11, 3, 11, 10},
				{7, 11, 3, 5, 13, 4, 7, 2},
				{4, 15, 15, 6, 1, 14, 14, 11},
				{5, 14, 10, 6, 3, 6, 15, 1},
				{2, 1, 12, 1, 4, 11, 3, 9}
};


void init_buffer(unsigned char *buffer, unsigned long long numbytes);

void fprint_bstr(FILE *fp, const char *label, const unsigned char *data, unsigned long long length);

int generate_test_vectors();

int main()
{
	int ret = generate_test_vectors();

	if (ret != KAT_SUCCESS) {
		fprintf(stderr, "test vector generation failed with code %d\n", ret);
	}

	return ret;
}


/*unsigned char FieldMult(unsigned char a, unsigned char b)
{
	const unsigned char ReductionPoly = 0x3;
	unsigned char x = a, ret = 0;
	int i;
	for(i = 0; i < 4; i++) {
		if((b>>i)&1) ret ^= x;
		if(x&0x8) {
			x <<= 1;
			x ^= ReductionPoly;
		}
		else x <<= 1;
	}
	return ret&WORDFILTER;
}*/


void print( unsigned char *m ) {

	/*printf("Ciphertext::\n");
	for( short i = 0; i < 64; ++i )
		printf("%2x ", m[ i ]);
		
	printf("\n\n");*/
	
	printf("Tag::\n");
	for( short i = 0; i < 32; ++i )
		printf("%02x ", m[ i ]);
		
	printf("\n\n");

	return;
}


void copy_ciphertext( unsigned char ct1[], unsigned char ct[] ) {

	for( short i = 0; i < 64; ++i )
		ct1[ i ] = ct[ i ];

	return;
}

void xor_of_diff_tag( uint8_t state[8][8], unsigned char ct1[] ) {

	uint8_t byte[ 32 ];
	short i, j, counter = 0;
	
	/*for( i = 0; i < 4; ++i ) {
	
		for( j = 0; j < 4; ++j ) {
		
			//byte[ counter ] = (( state[ i ][ j ] << 4 ) & 0xf0 ) ^ ( state[ i ][ j + 1 ] & 0x0f );
			byte[i*4+j]  = state[i][j*2  ] << 4;
			byte[i*4+j] |= state[i][j*2+1];
		}
	}*/
	
	memset(byte, 0, 32);
	for (i = 0; i < 64; i++)
	{
		byte[i / 2] |= (state[i / D][i % D] & 0xf) << (4 * (i & 1));
		//ct1[i / 2] |= ((state[i / D][i % D] & 0xf) << (4 * (i & 1)) );
	}
	
	counter = 0;
	for( i = 0; i < 32; ++i ) {
	
		ct1[ i ] ^= byte[ i ];
		++counter;
	}

	return;
}


void print_state( unsigned char state[8][8] ) {

	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", state[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");

	return;
}

void printDDT( unsigned char **ptr ) {


	for( int i = 0; i < 16; ++i ) {

		for( int j = 0; j < 16; ++j ) {

			printf("%d ", ptr[ i ][ j ]);
		}
		printf("\n");
	}

	return;
}


unsigned char **diffDistribution(unsigned char s[sboxSize]) {

	int i; 
	int x, y, delta, delta1;
	
	unsigned char** count = malloc(sboxSize*sizeof(int *));
	
	for(i = 0; i < sboxSize; ++i) {
		
		count[i] = malloc(sboxSize*sizeof(int));
		memset(count[i],0,sboxSize*sizeof(int));
	}
		
	for(y = 0; y < sboxSize; ++y) {
		
		for(x = 0; x < sboxSize; ++x) {
			
			delta = y^x;
			delta1 = s[x]^s[y];
			count[delta][delta1]++;
		}		
	}
	
	return count;
}

byte FieldMult1(byte a, byte b)
{
	byte x = a, ret = 0;
	int i;
	for(i = 0; i < S1; i++) {
		if((b>>i)&1) ret ^= x;
		if((x>>(S1-1))&1) {
			x <<= 1;
			x ^= ReductionPoly1;
		}
		else x <<= 1;
	}
	return ret&WORDFILTER1;
}

void invShiftRow(unsigned char state[D][D])
{
	int i, j;
	unsigned char tmp[D];
	for(i = 1; i < D; i++) {
		for(j = 0; j < D; j++)
			tmp[j] = state[i][j];
		for(j = 0; j < D; j++)
			state[i][j] = tmp[(j-i+D)%D];
	}
}


void ShiftRow1(byte state[D][D])
{
	int i, j;
	byte tmp[D];
	for(i = 1; i < D; i++) {
		for(j = 0; j < D; j++)
			tmp[j] = state[i][j];
		for(j = 0; j < D; j++)
			state[i][j] = tmp[(j+i)%D];
	}
}

void MixColumn1(byte state[D][D])
{
	int i, j, k;
	byte tmp[D];
	for(j = 0; j < D; j++){
		for(i = 0; i < D; i++) {
			byte sum = 0;
			for(k = 0; k < D; k++)
				sum ^= FieldMult1(MixColMatrix1[i][k], state[k][j]);
			tmp[i] = sum;
		}
		for(i = 0; i < D; i++)
			state[i][j] = tmp[i];
	}
}


void invMixColumn(unsigned char state[D][D])
{
	int i, j, k;
	unsigned char tmp[D];
	for(j = 0; j < D; j++){
		for(i = 0; i < D; i++) {
			unsigned char sum = 0;
			for(k = 0; k < D; k++)
				sum ^= FieldMult1(invMixColMatrix[i][k], state[k][j]);
			tmp[i] = sum;
		}
		for(i = 0; i < D; i++)
			state[i][j] = tmp[i];
	}
}


void Recover_state_columnwise( unsigned char known_diff, unsigned char pos, unsigned char count, unsigned char **ptr ) {

	unsigned char nfst[ 8 ][ 8 ], fst[ 8 ][ 8 ], temp[ 8 ][ 8 ], col[ 8 ][ 8 ];
	FILE *f0, *f1, *f2, *f3, *f4, *f5, *f6, *f7;
	unsigned char diff[ 8 ], diff1[ 8 ], delta, filename[ 24 ];
	unsigned char i, j;
	time_t t;

	srand( (unsigned) time( &t ) );

	for (i = 0; i < 64; i++)
	{
		nfst[i / 8][i % 8] = (tag1[i / 2] >> (4 * ((i & 1)))) & 0xf;
		fst[i / 8][i % 8] = (ftag[i / 2] >> (4 * ((i & 1)))) & 0xf;
		
		//state[i / D][i % D] = (state_inout[i / 2] >> (4 * (i & 1))) & 0xf;
	}
	
	for( i = 0; i < 8; ++i ) {
	
		for( j = 0; j < 8; ++j ) 
			temp[ i ][ j ] = nfst[ i ][ j ] ^ fst[ i ][ j ];
	}
	
	
	
	
	//print_state(nfst);
	//print_state(fst);
	
	//print_state(temp);
	/*printf("Full state difference::\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", temp[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");*/
	
	invMixColumn( temp );
	//print_state( temp );
	invShiftRow( temp );
	//print_state( temp );
	
	printf("Full state difference::\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", temp[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");
	
	printf("Right hand diff:\n");
	diff[ 0 ] = temp[ pos/8 ][ (pos%8) ];
	
	
	
	//state_inout[i / 2] |= (state[i / D][i % D] & 0xf) << (4 * (i & 1));
	
	
	
	printf("= %x\n", diff[0]);
		
	sprintf(filename, "key_column%d,%d,%d,0.txt", pos/8,(pos%8), count);
	if ((f0 = fopen(filename, "w+")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	for( i = 0; i < 16; ++i ) {
	
		
		//printf("0-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 0 ] ], diff[ 0 ]);
		//if( ( s[ i ] ^ s[ i ^ known_diff ] ) == diff[ 0 ] ) {
		if( ( ( s[ i ] ^ s[ i ^ 0x1 ] ) == diff[ 0 ] ) || ( ( s[ i ] ^ s[ i ^ 0x2 ] ) == diff[ 0 ] ) || ( ( s[ i ] ^ s[ i ^ 0x4 ] ) == diff[ 0 ] ) || ( ( s[ i ] ^ s[ i ^ 0x8 ] ) == diff[ 0 ] ) ) {
			
			printf("f0:: i = %x, diff = %x\n", i, diff[ 0 ]);
			fprint_bstr(f0, "", &i, 1);
		}
		
	}
	
	fclose( f0 );
		
	return;
}


unsigned short findMax( unsigned short arr[] ) {

	unsigned short max = 0;

	for( unsigned char i = 0; i < 16; ++i ) {
	
		if( max < arr[ i ] )
			max = arr[ i ];
	}

	return( max );
}


void state_nibble( unsigned char pos, unsigned char value ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	//int number = 8;
	//printf("State[%d]\n");
	
	printf("count = %d, ", value);
	for( unsigned char count = 0; count < value; ++count ) {
	
		sprintf(filename, "key_column%d,%d,%d,0.txt", pos/8,(pos%8),count);
		if ((fp1 = fopen(filename, "r+")) == NULL) {
			fprintf(stderr, "Couldn't open <%s> for read\n", filename);
			exit(1);
		}
		fseek(fp1, 0, SEEK_SET);
		while(fread(&val, 1, 1, fp1) == 1) {
		

			//printf ("val = %c", val);
			if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
				val = val - 97 + 10;
			else 
				val = val - 48;
				
			//printf ("......val = %x\n", val);
			
			arr[ val ] += 1;
		}
		//printf("\n");
		fclose( fp1 );
	}
	printf("Recovered nibble value at (%d,%d)-th position of the state::\n", pos/8, pos%8);
	printf("{ ");

	max = findMax( arr );
	printf("max = %d:: ", max);
	for( unsigned char i = 0; i < 16; ++i ) {

		if( arr[ i ] == max ) {
		
			printf("%x ", i );
			//printf("1st column = %04x\n", i);
			++count1;
		}
	}
	if( count1 >= 2 )
		gl_count += 1; 
	printf("}\n\n");
	
	return;
}


int generate_test_vectors()
{
	FILE                *fp;
	char                fileName[MAX_FILE_NAME];
	unsigned char       key[CRYPTO_KEYBYTES] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char		nonce[CRYPTO_NPUBBYTES] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char       msg[MAX_MESSAGE_LENGTH] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char       msg2[MAX_MESSAGE_LENGTH];
	unsigned char		ad[MAX_ASSOCIATED_DATA_LENGTH] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char		ct[MAX_MESSAGE_LENGTH + CRYPTO_ABYTES], ct1[MAX_MESSAGE_LENGTH + CRYPTO_ABYTES];
	//unsigned long long  clen, mlen2;
	//int                 count = 1;
	int                 func_ret, ret_val = KAT_SUCCESS;
	
	unsigned long long mlen, mlen2, clen, adlen;
	unsigned char diff, diff1, diff2, diff3, outdiff;
	uint8_t state[ 8 ][ 8 ], dstate[8][8];
	//unsigned char tag[ 16 ];
	unsigned char count = 0, pos = 0;
	unsigned char **ddt = diffDistribution(s);
	int i, j;
	uint8_t i1;
	
	
	time_t t;
	srand( (unsigned) time( &t ) );

	//init_buffer(key, sizeof(key));
	init_buffer(nonce, sizeof(nonce));
	init_buffer(msg, sizeof(msg));
	init_buffer(ad, sizeof(ad));
	
	mlen = adlen = mlen2 = 0;
	clen = 32;
	
	printDDT( &ddt[ 0 ] );
	
	printf("...............Encryption.....................\n");
	if ( crypto_aead_encrypt(ct, &clen, msg, mlen, ad, adlen, NULL, nonce, key) == 0)
		print(ct);
		
	/*for( i = mlen; i < mlen+32; ++i )
		tag[i-mlen] = ct[i];*/
		
	memcpy(tag1, ct, clen);
		
	if ( crypto_aead_decrypt(msg2, &mlen2, NULL, ct, clen, ad, adlen, nonce, key) == 0) {
	
		print(ct);
		printf("Decryption is successful!!\n\n\n");
	}
	else
		printf("Not successful!!\n\n\n");
	/*copy_ciphertext( ct1, ct );
	print(ct1);	
	if ( crypto_aead_decrypt(msg2, &mlen2, NULL, ct1, clen, ad, adlen, nonce, key) == 0) {
	
		print(ct);
		printf("Decryption1 is successful!!\n\n\n");
	}
	else
		printf("Not successful!!\n\n\n");*/
		
		
		
	count = 0;
	unsigned char token[4] = {0x1, 0x2, 0x4, 0x8};
	unsigned char token1[11] = {0x3, 0x5, 0x6, 0x7, 0x9, 0xa, 0xb, 0xc, 0xd, 0xe, 0xf};
	for( pos = 0; pos < 64; ++pos ) {
	
		//pos = 0;
		diff = rand() % 4;
		diff = token[diff];
		diff1 = diff;
	
		//printf("....................................................faulty forgery by injecting fault at the nibble position (%d,%d)...............................\n\n", pos/8, pos%8);	
		for( i1 = 1; i1 < 12; ++i1 ) {
		
			//printf("...................................................................................\n\n");
			for( i = 0; i < 8; ++i ) {

				for( j = 0; j < 8; ++j )
					state[ i ][ j ] = 0;
			}
			
			//if(pos%2 == 0)
			//outdiff = rand()%11;
			state[ pos / 8 ][ pos % 8 ] ^= token1[i1-1];
			/*else
				state[ pos / 8 ][ pos % 8 ] ^= ((i1&0xf)<<4);*/
			
			
			//printf("state difference before sr and mc:\n");
			//print_state( state );
			ShiftRow1(state);
			MixColumn1( state );
			//printf("state difference after sr and mc:\n");
			//print_state( state );
			//copy_ciphertext( ct1, ct );
			memcpy(ct1, ct, clen);
			//printf("non faulty tag::");print(ct1);
			xor_of_diff_tag( state, ct1 );
			//printf("faulty tag difference::");print(ct1);
			//print("in falty ecryption::\n");
			
			//printf("At %d-th query::\n", i1);
			//printf("fault in the dec query\n");	
			if ( faulty_aead_decrypt(msg2, &mlen2, NULL, ct1, clen, ad, adlen, nonce, key, diff, pos ) == 0 ) {
				
				printf("\n------------------------------------Tag Compare is successful!! at the position position = (%d, %d) with input diff = %x, output diff = %x\n\n", (pos/8), (pos%8),diff,token1[i1-1]);

				//printf("enter into the fun::Recover_state_columnwise\n");
				Recover_state_columnwise( diff, pos, count, &ddt[ 0 ] );
				//return 0;
				++count;
				
				if( count == 1) {
				
					diff2 = rand() % 4;
					diff2 = token[diff2];
					while(diff2 == diff1 ) {
						diff = rand() % 4;
						diff2 = token[diff];
					}
					//diff2 = token[diff];
					diff = diff2;
					i1 = 0;
				}
				
				
				if( count == 2) {
				
					diff3 = rand() % 4;
					diff3 = token[diff3];
					while( (diff3 == diff1 ) || (diff3 == diff2 )) {
					
						diff = rand() % 4;
						diff3 = token[diff];
					}
					//diff3 = token[diff];
					diff = diff3;
					i1 = 0;
				}
				
				
				/*printf("tag difference::\n\n");
				for(int k = 0; k < 32; ++k ) {
				
					if(k%4 == 0)
						printf("\n");
					printf("0x%02x, ", tag[k]^ftag[k]);
				}*/
				
				
			}
				
			//printf("\n\n");
			if(count == number)
				break;							
		}
		count = 0;
	}
			
	
	printf("faulty tag::\n");
	print(ct1);
	printf("Actual TAG DIFFERENCES:\n");
	for( i = 0; i < 16; ++i ) 
		printf("%x, ", ftag[i]^tag1[i]);
		
	printf("\nActual state values before s-box\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) {
		
			//dstate[i][j] = st[ i ][ j ]^st1[ i ][ j ];
			printf("%x ", st[ i ][ j ]);
		}
		
		printf("\n");
	}
	
	printf("\n");
	
		
	for( pos = 0; pos < 64; ++pos )
		state_nibble( pos, number );
		
	printf("Finally, the state space is reduced to 2^{%d}\n\n", gl_count);
	
	return 0;
}


void fprint_bstr(FILE *fp, const char *label, const unsigned char *data, unsigned long long length)
{    
    //fprintf(fp, "%s", label);
        
	for (unsigned long long i = 0; i < length; i++)
		fprintf(fp, "%x", data[i]);
	    
    //fprintf(fp, " ");
}

void init_buffer(unsigned char *buffer, unsigned long long numbytes)
{
	for (unsigned long long i = 0; i < numbytes; i++)
		buffer[i] = (unsigned char)(i+1);
}
