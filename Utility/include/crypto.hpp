#ifndef CRYPTO_COMMON
#define CRYPTO_COMMON

#include <vector>
#include <tuple>
#include "galois.hpp"
#include "matrix.hpp"

namespace crypto {

	struct Crypto_public_key {
	public:
		virtual ~Crypto_public_key() = 0;
		virtual matrix::Matrix<galois::Galois> encode(const matrix::Matrix<galois::Galois>& message) const = 0;

		virtual matrix::Matrix<galois::Galois> get_G() const = 0;
		virtual int get_n() const = 0;
		virtual int get_k() const = 0;
		virtual int get_t() const = 0;
	};

	struct Crypto_private_key {
	public:
		virtual ~Crypto_private_key() = 0;
		virtual matrix::Matrix<galois::Galois> decode(const matrix::Matrix<galois::Galois>& y) const = 0;
	};

	struct Cryptosystem {
	public:
		virtual ~Cryptosystem() = 0;
		virtual void generate_pair(Crypto_public_key **pub_k, Crypto_private_key **priv_k) const = 0;
	};

} // crypto

#endif // !CRYPTO_COMMON