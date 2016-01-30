//README

** This folder contains 3 files (server.c in server folder; client.c in client folder)

1. 201505587_assign_1_client.c
2. 201505587_assign_1_server.c
3. README


** Compile CLIENT as

gcc 201505587_assign_1_client.c -lm -lcrypto

("-lcrypto" parameter is required as I have used "openssl/sha.h" for caluculating the hash i.e. SHA1)


** Compile SERVER as

gcc 201505587_assign_1_server.c -lm -lcrypto

("-lcrypto" parameter is required as I have used "openssl/sha.h" for caluculating the hash i.e. SHA1)


** first run the server as

./a.out


** then client as

./a.out 127.0.0.1 <file_name>(optional)

(If file is not provided as the command line argument then it will be asked explicitly.)


