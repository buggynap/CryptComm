#include <sys/types.h>
#include <sys/wait.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>
#include <time.h>
#include <openssl/sha.h>

/* Global constants */
#define SERVICE_PORT 10010
#define MAX_SIZE 20
#define MAX_LEN 1024
#define SUCCESS 1
#define FAIL 0
#define DEFAULT_SERVER "127.0.0.1"
#define INPUT_ERROR 0
#define SYSCALL_ERROR 1
#define STACK_SIZE 10000
#define NOT_EXIST 0xFFFF;
#define LARGE 99
#define MAX_ITERATION 10 // Max tests in Miller-Robin Primality Test.
#define DIV /
#define MOD %
#define AND &&
#define TRUE 1
#define FALSE 0
#define Q_SIZE 5

#define PUBKEY 10 /* Public key message */
#define REQ 20  /* Request message */
#define REP 30  /* Reply message */
#define REQCOM 40  /* Request complete message */
#define DISCONNECT 50  /* Disconnect message */

/* Define a message structure */
typedef struct 
{
   int opcode;
   int src_addr;
   int dest_addr;
} Hdr;

/* RSA public key */
typedef struct 
{
   long int e; /* encryption exponent */
   long int n; /* modulus */
} PubKey;

/* A general message */
typedef struct 
{
   Hdr hdr; /* Header for a message */
   int status;
   char data[MAX_LEN];
   unsigned char sha1[SHA_DIGEST_LENGTH];
   PubKey pubkey;
} Msg;

typedef struct
{
   int top;
   char c[STACK_SIZE];
}stack;

typedef short boolean;

typedef union
{
   struct
   {
      long int n;
      long int e;
   } public_key;

   struct
   {
      long int n;
      long int d;
   } private_key;
} key;

int mul_inverse=0;
int gcd_value;
stack s;
int print_flag=0;
int print_flag1=0;
static int primeCorrect = 0;

int gcd(int a, int b);
void extended_euclid(int A1, int A2, int A3, int B1, int B2,int B3);
long int ModPower(long int x, long int e, long int n);
boolean MillerRobinTest(long int n, int iteration);
boolean verify_prime(long int p);
void decimal_to_binary(long int n,char str[]);
void reverse_string(char x[]);
long int ModPower(long int x, long int e, long int n);
void KeyGeneration(key *pub_key, key *pvt_key);
long int EncryptionAlgorithm(long int M, PubKey pub_key);
long int DecryptionAlgorithm(long int C, key pvt_key);
void ErrorHandler(int errorType, const char *msg);
long int encode(char c);
char * itoa(long int num);
void reverse(char str[], int length);
void swap(char *a, char *b);

void ErrorHandler(int errorType, const char *msg)
{
   if(errorType == SYSCALL_ERROR)
      perror(msg);
   else
      printf("%s\n",msg);
   exit(EXIT_FAILURE);
}

int gcd(int a, int b)
{
   int r;
   if(a < 0) a = -a;
   if(b < 0) b = -b;
   if(b == 0)
      return a;
   return gcd(b, a MOD b);
}

void extended_euclid(int A1, int A2, int A3, int B1, int B2,int B3)
{
   int Q;
   int T1,T2,T3;
   if(B3 == 0)
   {
      gcd_value = A3;
      mul_inverse = NOT_EXIST;
      return;
   }
   if(B3 == 1)
   {
      gcd_value = B3;
      mul_inverse = B2;
      return;
   }
   Q = (int)(A3/B3);
   T1 = A1 - Q*B1;
   T2 = A2 - Q*B2;
   T3 = A3 - Q*B3;
   A1 = B1;
   A2 = B2;
   A3 = B3;
   B1 = T1;
   B2 = T2;
   B3 = T3;
   extended_euclid(A1,A2,A3,B1,B2,B3);
}

boolean MillerRobinTest(long int n, int iteration)
{
   // n is the given integer and k is the given desired
   // number of iterations in this primality test algorithm.
   // Return TRUE if all the iterations test passed to give
   // the higher confidence that n is a prime, otherwise
   // return FALSE if n is composite.
   long int m, t;
   int i,j;
   long int a, u;
   int flag;
   if(n MOD 2 == 0)
      return FALSE;
   m = (n-1) DIV 2;
   t = 1;
   // n is composite.
   while( m MOD 2 == 0)
   {
      m = m DIV 2;
      t = t + 1;
      // repeat until m is even
   }
   for (j=0; j < iteration; j++) 
   { // Repeat the test for MAX_ITERATION times
      flag = 0;
      srand((unsigned int) time(NULL));
      a = random() MOD n + 1; // select a in {1,2,......,n}
      u = ModPower(a,m,n);
      if (u == 1 || u == n - 1)
         flag = 1;
      for(i=0;i<t;i++)
      {
         if(u == n - 1)
            flag = 1;
         u = (u * u) MOD n;
      }
      if ( flag == 0 )
         return FALSE; // n is composite
   }
   return TRUE; // n is prime.
} // end of MillerRobinTest().

//KEY GENERATION ALGORITHM IN RSA CRYPTOSYSTEM.
void KeyGeneration(key *pub_key, key *pvt_key)
{
   long int p,q;
   long int n;
   long int phi_n;
   long int e;
   // Select p and q which are primes and p<q.
   if(print_flag1)
      printf("\n selecting p->\n\r");
   while(1)
   {
      srand((unsigned int) time(NULL));
      p = random() % LARGE;
      /* test for even number */
      if ( p & 0x01 == 0 ) 
         continue;
      if(MillerRobinTest(p, MAX_ITERATION))
         break;
   }
   if(print_flag1)
      printf("\n selecting q->\n\r");
   while(1)
   {
      srand((unsigned int) time(NULL));
      q=random() % LARGE;
      if( q == p)
      {
         srand((unsigned int) time(NULL));
         q = random() % LARGE;
         continue;
      }
      if(MillerRobinTest(q, MAX_ITERATION))
      break;
   }
   // Compute n.
   if (verify_prime(p) && verify_prime(q) )
   {
      printf("p = %ld, q = %ld are primes\n", p, q);
      primeCorrect = 1;
   }
   else 
   {
    /*printf("p = %ld, q = %ld are composite\n", p, q);
      exit(0);*/
      primeCorrect = 0;
   }
   printf("p = %ld, q = %ld\n", p, q);
   n = p * q;
   // Compute Euler's phi(totient) function
   phi_n = (p-1)*(q-1);
   // Compute e such that gcd(e,phi_n(n))=1.
   if(print_flag1)
      printf("\n selcting e->\n\r");
   while(1)
   {
      e = random()%phi_n;
      if(gcd(e, phi_n)==1)
         break;
   }
   // Compute d such that ed=1(MOD phi_n(n)).
   if(print_flag1)
      printf("\n selceting d->\n\r");
   extended_euclid(1, 0, phi_n, 0, 1, e);
   if(mul_inverse <0) 
   {
      mul_inverse = - mul_inverse;
      mul_inverse = ((phi_n - 1 ) * mul_inverse) MOD phi_n;
   }
   if(print_flag1)
      printf("\n phi_n= %ld\n\n",phi_n);
   // Put Public Key and Private Key.
   pub_key->public_key.n = n;
   pub_key->public_key.e = e;
   pvt_key->private_key.n = n;
   pvt_key->private_key.d = mul_inverse;
} // end of KeyGeneraion()

boolean verify_prime(long int p)
{
   if(p == 1)
      return FALSE;

   long int d;
   // Test for p;
   for(d = 2; d <= (long int) sqrt(p); d++ )
      if ( p % d == 0 ) 
         return FALSE;
   return TRUE;
}

// Encryption Algorithm(E)
long int EncryptionAlgorithm(long int M, PubKey pub_key)
{
   // Alice computes ciphertext as C := M^e(MOD n) to Bob.
   long int C;
   if(print_flag1)
      printf("\n Encryption keys= ( %ld,%ld)\n\r",pub_key.n,pub_key.e);
   C = ModPower(M, pub_key.e, pub_key.n);
   return C;
}// Decryption Algorithm(D)

long int DecryptionAlgorithm(long int C, key pvt_key)
{
   // Bob retrieves M as M := C^d(MOD n)
   long int M;
   if(print_flag1)
      printf("\n Decryption keys= ( %ld,%ld)\n\r",pvt_key.private_key.n,pvt_key.private_key.d);
   M = ModPower(C, pvt_key.private_key.d, pvt_key.private_key.n);
   return M;
}

void decimal_to_binary(long int n,char str[])
{
   // n is the given decimal integer.
   // Purpose is to find the binary conversion
   // of n.
   // Initialise the stack.
   int r;
   s.top = 0;
   while(n != 0)
   {
      r = n MOD 2;
      s.top++;
      if(s.top >= STACK_SIZE)
      {
         printf("\nstack overflown!\n");
         return;
      }
      s.c[s.top] = r + 48;
      if(print_flag)
         printf("\n s.c[%d]= %c\n", s.top, s.c[s.top]);
      n = n DIV 2;
   }
   while(s.top)
   {
      *str++ = s.c[s.top--];
   }
   *str='\0';
   return;
}

// Algorithm: reverse a string.
void reverse_string(char x[])
{
   int n = strlen(x)-1;
   int i = 0;
   char temp[STACK_SIZE];
   for(i = 0; i<=n; i++)
      temp[i] = x[n-i];
   for(i=0; i<=n; i++)
      x[i] = temp[i];
}

// Algorithm: Modular Power: x^e(MOD n).
long int ModPower(long int x, long int e, long int n)
{// To calculate y:=x^e(MOD n).
//long y;
   long int y;
   long int t;
   int i;
   int BitLength_e;
   char b[STACK_SIZE];
   //printf("e(decimal) = %ld\n",e);
   decimal_to_binary(e,b);
   if(print_flag)
      printf("b = %s\n", b);
   BitLength_e = strlen(b);
   y = x;
   reverse_string(b);
   for(i = BitLength_e - 2; i >= 0 ; i--)
   {
      if(print_flag)
         printf("\nb[%d]=%c", i, b[i]);
      if(b[i] == '0')
         t = 1;
      else t = x;
         y = (y * y) MOD n;
      if ( y < 0 ) 
      {
         y = -y;
         y = (y - 1) * (y MOD n) MOD n;
         printf("y is negative\n");
      }
      y = (y*t) MOD n;
      if ( y < 0 ) 
      {
         y = -y;
         y = (y - 1) * (y MOD n) MOD n;
         printf("y is negative\n");
      }
   }
   if ( y < 0 ) 
   {
      y = -y;
      y = (y - 1) * (y MOD n) MOD n;
      printf("y is negative\n");
   }
   return y;
} // end of ModPower().

//-----------------------------------------------------------------------------------------------------------/

/* Function prototypes */
int startServer ( );
void Talk_to_client ( int );
void serverLoop ( int );

/* Start the server: socket(), bind() and listen() */
int startServer ()
{
   int sfd;                    /* for listening to port PORT_NUMBER */
   struct sockaddr_in saddr;   /* address of server */
   int status;


   /* Request for a socket descriptor */
   sfd = socket(AF_INET, SOCK_STREAM, 0);
   if (sfd == -1) {
      fprintf(stderr, "*** Server error: unable to get socket descriptor\n");
      exit(1);
   }

   /* Set the fields of server's internet address structure */
   saddr.sin_family = AF_INET;            /* Default value for most applications */
   saddr.sin_port = htons(SERVICE_PORT);  /* Service port in network byte order */
   saddr.sin_addr.s_addr = INADDR_ANY;    /* Server's local address: 0.0.0.0 (htons not necessary) */
   bzero(&(saddr.sin_zero),8);            /* zero the rest of the structure */

   /* Bind the socket to SERVICE_PORT for listening */
   status = bind(sfd, (struct sockaddr *)&saddr, sizeof(struct sockaddr));
   if (status == -1) {
      fprintf(stderr, "*** Server error: unable to bind to port %d\n", SERVICE_PORT);
      exit(2);
   }

   /* Now listen to the service port */
   status = listen(sfd,Q_SIZE);
   if (status == -1) {
      fprintf(stderr, "*** Server error: unable to listen\n");
      exit(3);
   }

   fprintf(stderr, "+++ Server successfully started, listening to port %hd\n", SERVICE_PORT);
   return sfd;
}

/* Accept connections from clients, spawn a child process for each request */
void serverLoop ( int sfd )
{
	int cfd;                    /* for communication with clients */
	struct sockaddr_in caddr;   /* address of client */
	int size;

    while (1) 
    {
		/* accept connection from clients */
		cfd = accept(sfd, (struct sockaddr *)&caddr, (unsigned int*) &size);
		if (cfd == -1) 
		{
			fprintf(stderr, "*** Server error: unable to accept request\n");
			continue;
		}
     	printf("**** Connected with %s\n", inet_ntoa(caddr.sin_addr));
     	/* fork a child to process request from client */
//      	if (!fork()) 
    //  	{
        	Talk_to_client (cfd);
  //       	fprintf(stderr, "**** Closed connection with %s\n", inet_ntoa(caddr.sin_addr));
    //     	close(cfd);
      //   	exit(0);
      	//}
		/* parent (server) does not talk with clients */
      	close(cfd);
      	/* parent waits for termination of child processes */
      //	while (waitpid(-1,NULL,WNOHANG) > 0);
   	}
}

/* Interaction of the child process with the client */
void Talk_to_client ( int cfd )
{
	int status;
   	int nbytes;
   	int src_addr, dest_addr;
   	Msg send_msg;
   	Msg recv_msg;
   	PubKey clientPublicKey;

   	dest_addr = inet_addr("127.0.0.1");
   	src_addr = inet_addr(DEFAULT_SERVER);
 
	while (1) 
   	{
		/* Receive response from client */
		nbytes = recv(cfd, &recv_msg, sizeof(Msg), 0);

		if (nbytes == -1) 
		{
			fprintf(stderr, "*** Server error: unable to receive\n");
			return;
		}
		switch ( recv_msg.hdr.opcode ) 
		{
			
         case PUBKEY : /* Public Key Message */
				printf("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
				printf("Message:: with opcode %d (PUBKEY) received from source (%d)\n", recv_msg.hdr.opcode, recv_msg.hdr.src_addr);  
				printf("Received public key\n");
				printf("Pub Key n : %ld\t", recv_msg.pubkey.n);
				printf("Pub Key e : %ld\n" , recv_msg.pubkey.e);
				
            //assign the values to the client Public Key structure
				clientPublicKey.e = recv_msg.pubkey.e;
				clientPublicKey.n = recv_msg.pubkey.n;
				break;

         case REQ: /* Request file message */
				printf("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
				printf("Message:: with opcode %d (REQ) received from source (%d)\n", recv_msg.hdr.opcode, recv_msg.hdr.src_addr);
            printf("Requested file name : \"%s\"", recv_msg.data);

				FILE *fp;
				fp = fopen(recv_msg.data, "r");
				if(fp == NULL)
				{
					printf("File is not present...\n");
					printf("Sending DISCONNECT message to the client\n");
					send_msg.hdr.opcode = DISCONNECT;
           		send_msg.hdr.src_addr = src_addr;
           		send_msg.hdr.dest_addr = dest_addr;
           		send_msg.status = FAIL;
           		memset(send_msg.data, '\0', MAX_LEN);
              		memset(send_msg.sha1, '\0', MAX_LEN);
					send_msg.pubkey.e = 0;
					send_msg.pubkey.n = 0;
					status = send(cfd, &send_msg, sizeof(Msg), 0);
					if (status == -1) 
					{
						fprintf(stderr, "*** Client error: unable to send\n");
						return;
					}
					exit(0);
				}
				else
				{
					printf("Requested file found on server...\nStarting the encryption...\n");
					long int blockSize = 16, counter = 0, intermediateNumber, flag = 0, j;
					char c, encryptedData[MAX_LEN], intermediateString[MAX_LEN], orgData[MAX_LEN];
					unsigned char hash[SHA_DIGEST_LENGTH];
               memset(encryptedData, '\0', sizeof encryptedData);
               memset(orgData, '\0', sizeof orgData);
               memset(hash, '\0', sizeof hash);
					while((c = fgetc(fp)) != EOF)
					{
						if(counter == blockSize)
						{
							//Generate the hash for the original data and send encrypted data to the client
							printf("++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
                     printf("Encrypted data : %s\n", encryptedData);
                     printf("original data : %s\n", orgData);

                     SHA1(orgData, sizeof(orgData) - 1, hash);

							printf("SHA1 -> ");
							for(j = 0; j < SHA_DIGEST_LENGTH; j++)
							  printf("%u", hash[j]);

							//Send the data to client
							printf("\nSending data...\n");
							send_msg.hdr.opcode = REP;
           				send_msg.hdr.src_addr = src_addr;
           				send_msg.hdr.dest_addr = dest_addr;
           				send_msg.status = SUCCESS;
           				//copy the data 
           				strcpy(send_msg.data, encryptedData);
           				//copy the sha1
           				for(j = 0; j < SHA_DIGEST_LENGTH; j++)
           					send_msg.sha1[j] = hash[j];
							send_msg.pubkey.e = 0;
							send_msg.pubkey.n = 0;
							status = send(cfd, &send_msg, sizeof(Msg), 0);
							if (status == -1) 
							{
								fprintf(stderr, "*** Client error: unable to send\n");
								return;
							}
							//data sent
							counter = 0;
							memset(encryptedData, '\0', sizeof encryptedData);
							memset(orgData, '\0', sizeof orgData);
                     memset(hash, '\0', sizeof hash);
							flag = 1;
						}
						orgData[counter] = c;
						intermediateNumber = EncryptionAlgorithm(encode(c), recv_msg.pubkey);
						
                  int i = 0;
						//Convert the number to the string here
						while(intermediateNumber != 0)
						{
							intermediateString[i++] = intermediateNumber % 10 + '0';
							intermediateNumber /= 10;
						}
						intermediateString[i] = '\0';
						reverse_string(intermediateString);
						strcat(encryptedData, intermediateString);

						strcat(encryptedData, ",");

						flag = 0;
						counter++;
					}

					if(flag == 0)  // means the data is formed less than the block size
					{
                  printf("Encrypted data : %s\n", encryptedData);
                  printf("Original data : %s\n", orgData );
						SHA1(orgData, sizeof(orgData) - 1, hash);
						printf("SHA1\n");
						for(j = 0; j < SHA_DIGEST_LENGTH; j++)
						   printf("%u", hash[j]);
						//Sending the data
						printf("Sending data...\n");
						send_msg.hdr.opcode = REP;
       				send_msg.hdr.src_addr = src_addr;
       				send_msg.hdr.dest_addr = dest_addr;
       				send_msg.status = SUCCESS;
       				//copy the data 
       				strcpy(send_msg.data, encryptedData);
       				//copy the sha1
       				for(j = 0; j < SHA_DIGEST_LENGTH; j++)
       					send_msg.sha1[j] = hash[j];
						send_msg.pubkey.e = 0;
						send_msg.pubkey.n = 0;
						status = send(cfd, &send_msg, sizeof(Msg), 0);
						if (status == -1) 
						{
							fprintf(stderr, "*** Client error: unable to send\n");
							return;
						}
               }

					//  File data transferred completely
               //    Send the DISCONNECT message to the client and close
					printf("Sending REQCOMM message to the client\n");
					send_msg.hdr.opcode = REQCOM;
           		send_msg.hdr.src_addr = src_addr;
           		send_msg.hdr.dest_addr = dest_addr;
           		send_msg.status = SUCCESS;
           		memset(send_msg.data, '\0', MAX_LEN);
           		memset(send_msg.sha1, '\0', MAX_LEN);
					send_msg.pubkey.e = 0;
					send_msg.pubkey.n = 0;
					status = send(cfd, &send_msg, sizeof(Msg), 0);
					if (status == -1) 
					{
						fprintf(stderr, "*** Client error: unable to send\n");
						return;
					}
					fclose(fp);
				}
				break;

			case DISCONNECT:
				printf("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
				printf("Message:: with opcode %d (DISCONNECT) received from source (%d)\n", recv_msg.hdr.opcode, recv_msg.hdr.src_addr);
				printf("Exiting...\n");
				exit(0);

			default: 
				printf("message received with opcode: %d\n", recv_msg.hdr.opcode);
				exit(0);  
		}
 	}
}

char* itoa(long int no)
{
	long i = 0, j = 0, temp;
	char *str;
	while(no != 0)
	{
		str[i++] = no % 10 + '0';
		no /= 10;
	}
	str[i] = '\0';
	reverse(str, i - 1);
	str[i] = '\0';
}

/* A utility function to reverse a string  */
void reverse(char str[], int length)
{
    int start = 0;
    int end = length -1;
    while (start < end)
    {
    	char c;
    	c = *(str+start);
    	*(str+start) = *(str+end);
    	*(str+end) = c;
        start++;
        end--;
    }
}

long int encode(char c)
{
	if(c == ' ')
		return 0;
	else if (c >= 'A' && c <= 'Z')
		return c - 'A' + 1;
	else if (c >= 'a' && c <= 'z')
		return c - 'a' + 27;
	else if (c >= '0' && c <= '9')
		return c- '0' + 53;
	else if (c == ',')
		return 63;
	else if (c == '.')
		return 64;
	else if (c == '!')
		return 65;
	return 66;
}
//-----------------------------------------------------------------------------------------------------------

int main(int argc, char *argv[])
{
	int sfd = startServer();   
   	serverLoop(sfd);
   	close(sfd);
   	return 0;
}
