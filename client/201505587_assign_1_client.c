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

/* RSA public key */
typedef struct 
{
   long int d; /* decryption exponent */
   long int n; /* modulus */
} PriKey;

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
long int EncryptionAlgorithm(long int M, key pub_key);
long int DecryptionAlgorithm(long int C, PriKey pvt_key);
void ErrorHandler(int errorType, const char *msg);
char decode(long int c);

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
long int EncryptionAlgorithm(long int M, key pub_key)
{
   // Alice computes ciphertext as C := M^e(MOD n) to Bob.
   long int C;
   if(print_flag1)
      printf("\n Encryption keys= ( %ld,%ld)\n\r",pub_key.public_key.n,pub_key.public_key.e);
   C = ModPower(M, pub_key.public_key.e, pub_key.public_key.n);
   return C;
}// Decryption Algorithm(D)

long int DecryptionAlgorithm(long int C, PriKey pvt_key)
{
   // Bob retrieves M as M := C^d(MOD n)
   long int M;
   if(print_flag1)
      printf("\n Decryption keys= ( %ld,%ld)\n\r",pvt_key.n,pvt_key.d);
   M = ModPower(C, pvt_key.d, pvt_key.n);
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

int serverConnect ( char * );
void Talk_to_server ( int cfd, PubKey publicKey, char* fileName, PriKey privateKey);

/* Connect with the server: socket() and connect() */
int serverConnect ( char *sip )
{
   int cfd;
   struct sockaddr_in saddr; /* address of server */
   int status;

   /* request for a socket descriptor */
   cfd = socket (AF_INET, SOCK_STREAM, 0);
   if (cfd == -1) 
   {
      fprintf (stderr, "*** Client error: unable to get socket descriptor\n");
      exit(1);
   }

   /* set server address */
   saddr.sin_family = AF_INET;              /* Default value for most applications */
   saddr.sin_port = htons(SERVICE_PORT);    /* Service port in network byte order */
   saddr.sin_addr.s_addr = inet_addr(sip);  /* Convert server's IP to short int */
   bzero(&(saddr.sin_zero),8);              /* zero the rest of the structure */

   /* set up connection with the server */
   status = connect(cfd, (struct sockaddr *)&saddr, sizeof(struct sockaddr));
   if (status == -1) 
   {
      fprintf(stderr, "*** Client error: unable to connect to server\n");
      exit(1);
   }

   fprintf(stderr, "Connected to server\n");

   return cfd;   
}

/* Interaction with the server */
void Talk_to_server ( int cfd, PubKey publicKey, char* fileName, PriKey privateKey)
{
   char buffer[MAX_LEN];
   int nbytes, status;
   int src_addr, dest_addr;
   Msg send_msg;
   Msg recv_msg;

   dest_addr = inet_addr(DEFAULT_SERVER);
   src_addr = inet_addr("127.0.0.1");

   /* send the public key message PUBKEY to the server */
   printf("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
   printf("Sending the request message PUBKEY to the server\n");
   send_msg.hdr.opcode = PUBKEY;
   send_msg.hdr.src_addr = src_addr;
   send_msg.hdr.dest_addr = dest_addr;
   send_msg.status = SUCCESS;
   memset(send_msg.data, '\0', MAX_LEN);
   memset(send_msg.sha1, '\0', MAX_LEN);
   send_msg.pubkey = publicKey;   
   status = send(cfd, &send_msg, sizeof(Msg), 0);

   if (status == -1) 
   {
      fprintf(stderr, "*** Server error: unable to send\n");
      return;
   }

   /* send the message REQ to the server */
   //Send the public key to the server
   printf("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
   printf("Sending the request message REQ to the server\n");
   send_msg.hdr.opcode = REQ;
   send_msg.hdr.src_addr = src_addr;
   send_msg.hdr.dest_addr = dest_addr;
   send_msg.status = SUCCESS;
   memset(send_msg.data, '\0', MAX_LEN);
   strcpy(send_msg.data, fileName);
   memset(send_msg.sha1, '\0', MAX_LEN);
   send_msg.pubkey = publicKey;
   status = send(cfd, &send_msg, sizeof(Msg), 0);

   int firstTime = TRUE;
   FILE *fp = NULL;
   
   if (status == -1) 
   {
      fprintf(stderr, "*** Server error: unable to send\n");
      return;
   }

   while (1) 
   {
      /* receive greetings from server */
      nbytes = recv(cfd, &recv_msg, sizeof(Msg), 0);
      if (nbytes == -1) 
      {
         fprintf(stderr, "*** Client error: unable to receive\n");
      }
      switch ( recv_msg.hdr.opcode ) 
      {
         case REP:
            if(firstTime == TRUE)
            {
               fp = fopen(fileName, "w+");
               if(fp == NULL)
               {
                  printf("Unable to create file at the destination...\n");
                  return;
               }
               firstTime = FALSE;
            }
            printf("Message:: with opcode %d (REP) received from source (%d)\n", recv_msg.hdr.opcode, recv_msg.hdr.src_addr);  
            /* Check the status of REP message */
            if (recv_msg.status) 
            {
               printf("++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
               printf("Data received from the server...\n");
               printf("Encrypted data : %s\n", recv_msg.data);
               printf("SHA1 -> ");
               int j;
               for(j = 0; j < SHA_DIGEST_LENGTH; j++)
                     printf("%u", recv_msg.sha1[j]);
               
               char encryptedData[MAX_LEN], temp[128], orgData[MAX_LEN], orgChar;
               int i, counter = 0, flag = 0, wordCounter = 0;
               unsigned char hash[SHA_DIGEST_LENGTH];
               strcpy(encryptedData, recv_msg.data);
               //change the comma seperated value to the normal text and one for every character and decode it
               for(i = 0; i < strlen(encryptedData); i++)
               {
                  if(encryptedData[i] == ',')
                  {
                     temp[counter] = '\0';
                     //printf("%s",temp);
                     long int decValue = DecryptionAlgorithm(atol(temp), privateKey);
                     orgChar = decode(DecryptionAlgorithm(atol(temp), privateKey));
                     //printf("%ld",DecryptionAlgorithm(atol(temp), privateKey));
                     //printf(" decoded Value : %c",(orgChar = decode(DecryptionAlgorithm(atol(temp), privateKey))));
                     orgData[wordCounter++] = orgChar;
                     fputc(orgChar, fp);

                     counter = 0;
                     flag = 1;
                  }
                  else
                  {
                     temp[counter++] = encryptedData[i];
                     flag = 0;
                  }
               }
               orgData[wordCounter] = '\0';
               fputc(orgChar, fp);
      
               int isCorrect = TRUE;

               SHA1(orgData, sizeof(orgData) - 1, hash);

               printf("\nOriginal data : %s ", orgData);

               //Check the hash
               printf("\nChecking the hash : \n");

               printf("Calculated hash : ");
               for(j = 0; j < SHA_DIGEST_LENGTH; j++)
                  printf("%u", hash[j]);
               for(j = 0; j < SHA_DIGEST_LENGTH; j++)
                     if(recv_msg.sha1[j] != hash[j])
                     {
                        isCorrect = FALSE;
                        break;
                     }
               if(isCorrect == TRUE)
                  printf("\n[SHA Matched]\n");
               else
               {
                  printf("++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
                  printf("[SHA NOT Matched]\n");
                  //Send the disconnect message to the server and shutdown client
                  printf("Sending DISCONNECT message to the server\n");
                  send_msg.hdr.opcode = DISCONNECT;
                  send_msg.hdr.src_addr = src_addr;
                  send_msg.hdr.dest_addr = dest_addr;
                  send_msg.status = SUCCESS;
                  memset(send_msg.data, '\0', MAX_LEN);
                  strcpy(send_msg.data, fileName);
                  memset(send_msg.sha1, '\0', MAX_LEN);
                  send_msg.pubkey = publicKey;
                  status = send(cfd, &send_msg, sizeof(Msg), 0);

                  if (status == -1) 
                  {
                     fprintf(stderr, "*** Server error: unable to send\n");
                     return;
                  }
                  printf("Exiting...\n");
                  exit(0);
               }

               memset(hash, '\0', sizeof hash);
               memset(orgData, '\0', sizeof orgData);
               wordCounter = 0;


               printf("\n");
            }
            else
            {
               printf("Message REQ has NOT received successfully by the server\n");
            }
            break;
         case REQCOM : 
            fclose(fp);
            printf("Message:: with opcode %d (REQCOM) received from source (%d)\n", recv_msg.hdr.opcode, recv_msg.hdr.src_addr);  
              /* Check the status of REP message */
            if (recv_msg.status)
            {
               printf("++++++++++++++++++++++++++++++++++++++++++++++++++++\n");
               printf("\"%s\" File successfully downloaded...\n", fileName);
               printf("Sending DISCONNECT message to the server\n");
               send_msg.hdr.opcode = DISCONNECT;
               send_msg.hdr.src_addr = src_addr;
               send_msg.hdr.dest_addr = dest_addr;
               send_msg.status = SUCCESS;
               memset(send_msg.data, '\0', MAX_LEN);
               strcpy(send_msg.data, fileName);
               memset(send_msg.sha1, '\0', MAX_LEN);
               send_msg.pubkey = publicKey;
               status = send(cfd, &send_msg, sizeof(Msg), 0);

               if (status == -1) 
               {
                  fprintf(stderr, "*** Server error: unable to send\n");
                  return;
               }
               printf("Exiting...\n");
               exit(0);
            }
            else    
               printf("Message REQ has NOT received successfully by the server\n");
            break;
         case DISCONNECT : 
            printf("Message:: with opcode %d (DISCONNECT) received from source (%d)\n", recv_msg.hdr.opcode, recv_msg.hdr.src_addr);
            /* Check the status of REP message */

            if (recv_msg.status == FAIL) 
               printf("\"%s\" File is not present on server\n", fileName);
            else 

            printf("Exiting...\n");

            exit(0);

            break;
         default: 
            printf("message received with opcode: %d\n", recv_msg.hdr.opcode);
            //sleep(1000);
            //exit(0);  
      }
   }
}

char decode(long int c)
{
   if(c == 0)
      return 0;
   else if (c >= 1 && c <= 26)
      return (char) (c + 'A' - 1);
   else if (c >= 27 && c <= 52)
      return (char) (c + 'a' - 27);
   else if (c >= 53 && c <= 62)
      return (char) (c + '0' - 53);
   else if (c == 63)
      return ',';
   else if (c == 64)
      return '.';
   else if (c == 65)
      return '!';
   return '\n';
}

//-----------------------------------------------------------------------------------------------------------

int main(int argc, char *argv[])
{
   int sock, n;
   unsigned int length;
   struct sockaddr_in server, from;
   struct hostent *hostName;
   char buffer[256];
   char fileName[256];
   char str[STACK_SIZE];
   int x, e;
   char ch;
   key pub_key, pvt_key;
   PubKey publicKey;
   PriKey privateKey;


   //Check for the argument
   if(argc != 3)
   {
      if(argc == 2)
      {
         printf("\nEnter the file name : ");
         scanf("%s", fileName);
      }
      else
      {
         ErrorHandler(INPUT_ERROR, "Usage: \"a.out <server_ip> <file_name>(optional)\"\n");   
      }
   }
   else if(argc == 3)
   {
      strcpy(fileName, argv[2]);
   }
   else
   {
      ErrorHandler(INPUT_ERROR, "Usage: \"a.out <server_ip> <file_name>(optional)\"\n");   
   }

   //Generate the key
   printf("\nKey generaion has been strated by Alice:\n\r");

   while(primeCorrect != 1)
   {
      KeyGeneration(&pub_key, &pvt_key);
   }

   printf("\n Public Key of Alice is (n,e): (%ld , %ld)\n\r", pub_key.public_key.n, pub_key.public_key.e);

   publicKey.n = pub_key.public_key.n;
   publicKey.e = pub_key.public_key.e;

   printf("\n Private key of Alice is (n,d): (%ld , %ld)\n\r", pvt_key.private_key.n,pvt_key.private_key.d);

   privateKey.n = pvt_key.private_key.n;
   privateKey.d = pvt_key.private_key.d;

   //Start the communication process
   char sip[16];
   int cfd;

   strcpy(sip, (argc == 2) ? argv[1] : DEFAULT_SERVER);
   cfd = serverConnect(sip);
   Talk_to_server(cfd, publicKey, fileName, privateKey);

   close(cfd);

   return 0;
}