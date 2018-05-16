#ifndef DIAGONAL_CONSTR
#define DIAGONAL_CONSTR

#include <vector>
#include <tuple>
#include "galois.hpp"
#include "matrix.hpp"
#include "crypto.hpp"

namespace diagonal_construction {

	struct Diagonal_public : public crypto::Crypto_public_key{
	public:
		Diagonal_public();
		Diagonal_public(const matrix::Matrix<galois::Galois>& G, const matrix::Matrix<galois::Galois>& W);
		~Diagonal_public();
		matrix::Matrix<galois::Galois> encode(const matrix::Matrix<galois::Galois>& message) const;

		matrix::Matrix<galois::Galois> get_G() const;
		matrix::Matrix<galois::Galois> get_W() const;
		int get_n() const;
		int get_k() const;
		int get_t() const;

	private:
		int t;
		matrix::Matrix<galois::Galois> G;
		matrix::Matrix<galois::Galois> W;
	};

	struct Diagonal_private : public crypto::Crypto_private_key {
	public:
		Diagonal_private();
		Diagonal_private(const matrix::Matrix<galois::Galois>& M_inv,
			const crypto::Crypto_private_key* decoder);
		~Diagonal_private();
		matrix::Matrix<galois::Galois> decode(const matrix::Matrix<galois::Galois>& y) const;

	private:
		matrix::Matrix<galois::Galois> M_inv;
		const crypto::Crypto_private_key *decoder;
	};

	struct Diagonal : public crypto::Cryptosystem {
	public:
		Diagonal(const Cryptosystem &decoder);
		~Diagonal();
		void generate_pair(crypto::Crypto_public_key **pub_k, crypto::Crypto_private_key **priv_k) const;

	private:
		const crypto::Cryptosystem *decoder;
	};

} // diagonal_construction

#endif // !DIAGONAL_CONSTR