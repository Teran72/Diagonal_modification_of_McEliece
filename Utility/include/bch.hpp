#ifndef BCH_KEY
#define BCH_KEY

#include <vector>
#include <tuple>
#include "galois.hpp"
#include "matrix.hpp"
#include "crypto.hpp"

namespace bch {

	struct BCH_public : public crypto::Crypto_public_key {
	public:
		BCH_public();
		BCH_public(int t, const matrix::Matrix<galois::Galois>& G_0);
		~BCH_public();
		matrix::Matrix<galois::Galois> encode(const matrix::Matrix<galois::Galois>& message) const;

		matrix::Matrix<galois::Galois> get_G() const;
		int get_n() const;
		int get_k() const;
		int get_t() const;

		matrix::Matrix<galois::Galois> add_errors(const matrix::Matrix<galois::Galois>& y) const;

	private:
		int t;
		matrix::Matrix<galois::Galois> G_0;
	};

	struct BCH_private : public crypto::Crypto_private_key {
	public:
		BCH_private();
		BCH_private(int t, unsigned int poly, const matrix::Matrix<galois::Galois>& G_0_inv);
		~BCH_private();
		matrix::Matrix<galois::Galois> decode(const matrix::Matrix<galois::Galois>& y) const;

	private:
		int t;
		unsigned int poly;
		matrix::Matrix<galois::Galois> G_0_inv;
	};

	struct BCH : public crypto::Cryptosystem {
	public:
		BCH(int n);
		~BCH();
		void generate_pair(crypto::Crypto_public_key **pub_k, crypto::Crypto_private_key **priv_k) const;

	private:
		static matrix::Matrix<galois::Galois> make_bch(const std::vector<galois::Galois>& g);
		static std::vector<galois::Galois> mulPolynoms(const std::vector<std::vector<galois::Galois> >& gs, int n);

		int n;
	};

} // bch

#endif // !BCH_KEY