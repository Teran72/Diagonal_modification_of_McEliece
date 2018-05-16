#ifndef MCELIECE
#define MCELIECE

#include <vector>
#include <tuple>
#include "galois.hpp"
#include "matrix.hpp"
#include "crypto.hpp"

namespace mceliece {

	struct McEliece_public : public crypto::Crypto_public_key{
	public:
		McEliece_public();
		McEliece_public(int t, const matrix::Matrix<galois::Galois>& G);
		~McEliece_public();
		matrix::Matrix<galois::Galois> encode(const matrix::Matrix<galois::Galois>& message) const;

		matrix::Matrix<galois::Galois> get_G() const;
		int get_n() const;
		int get_k() const;
		int get_t() const;

	private:
		int t;
		matrix::Matrix<galois::Galois> G;
	};

	struct McEliece_private : public crypto::Crypto_private_key {
	public:
		McEliece_private();
		McEliece_private(const matrix::Matrix<galois::Galois>& M_inv,
			const matrix::Matrix<galois::Galois>& P_inv,
			const crypto::Crypto_private_key* decoder);
		~McEliece_private();
		matrix::Matrix<galois::Galois> decode(const matrix::Matrix<galois::Galois>& y) const;

	private:
		matrix::Matrix<galois::Galois> M_inv;
		matrix::Matrix<galois::Galois> P_inv;
		const crypto::Crypto_private_key *decoder;
	};

	struct McEliece : public crypto::Cryptosystem {
	public:
		McEliece(const Cryptosystem &decoder);
		~McEliece();
		void generate_pair(crypto::Crypto_public_key **pub_k, crypto::Crypto_private_key **priv_k) const;

	private:
		const crypto::Cryptosystem *decoder;
	};

} // mceliece

#endif // !MCELIECE