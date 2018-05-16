#include "crypto.hpp"

using namespace crypto;

Crypto_public_key::~Crypto_public_key() {}

Crypto_private_key::~Crypto_private_key() {}

Cryptosystem::~Cryptosystem() {}

//void Cryptosystem::generate_pair(Crypto_public_key **pub_k, Crypto_private_key **priv_k,
//	int n, const Cryptosystem* decoder) {
//	return;
//}