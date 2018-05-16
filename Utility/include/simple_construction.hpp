#ifndef SIMPLE_CONSTR
#define SIMPLE_CONSTR

#include <vector>
#include <tuple>
#include "galois.hpp"
#include "matrix.hpp"
#include "crypto.hpp"

namespace simple_construction {

	struct Simple_public : public crypto::Crypto_public_key{
	public:
		Simple_public();
		Simple_public(int t, const matrix::Matrix<galois::Galois>& G, const matrix::Matrix<galois::Galois>& M_1);
		~Simple_public();
		matrix::Matrix<galois::Galois> encode(const matrix::Matrix<galois::Galois>& message) const;

		matrix::Matrix<galois::Galois> get_G() const;
		matrix::Matrix<galois::Galois> get_M_1() const;
		int get_n() const;
		int get_k() const;
		int get_t() const;

	private:
		int t;
		matrix::Matrix<galois::Galois> G;
		matrix::Matrix<galois::Galois> M_1;
	};

	struct Simple_private : public crypto::Crypto_private_key {
	public:
		Simple_private();
		Simple_private(const matrix::Matrix<galois::Galois>& M_inv,
			const crypto::Crypto_private_key* decoder);
		~Simple_private();
		matrix::Matrix<galois::Galois> decode(const matrix::Matrix<galois::Galois>& y) const;

	private:
		matrix::Matrix<galois::Galois> M_inv;
		const crypto::Crypto_private_key *decoder;
	};

	struct Simple : public crypto::Cryptosystem {
	public:
		Simple(const Cryptosystem &decoder);
		~Simple();
		void generate_pair(crypto::Crypto_public_key **pub_k, crypto::Crypto_private_key **priv_k) const;

	private:
		const crypto::Cryptosystem *decoder;
	};

} // simple_construction

#endif // !SIMPLE_CONSTR