#ifndef GOPPA
#define GOPPA

#include <vector>
#include <string>
#include "galois.hpp"
#include "matrix.hpp"
#include "crypto.hpp"

namespace goppa {

	struct Goppa_public : public crypto::Crypto_public_key {
	public:
		Goppa_public();
		Goppa_public(int t, const matrix::Matrix<galois::Galois>& G);
		~Goppa_public();
		matrix::Matrix<galois::Galois> encode(const matrix::Matrix<galois::Galois>& message) const;

		matrix::Matrix<galois::Galois> get_G() const;
		int get_n() const;
		int get_k() const;
		int get_t() const;

		matrix::Matrix<galois::Galois> add_errors(const matrix::Matrix<galois::Galois>& y) const;

	private:
		int t;
		matrix::Matrix<galois::Galois> G;
	};

	struct Goppa_private : public crypto::Crypto_private_key {
	public:
		Goppa_private();
		Goppa_private(unsigned int poly, const matrix::Matrix<galois::Galois>& g,
			const matrix::Matrix<galois::Galois>& H, const matrix::Matrix<galois::Galois>& Y,
			const matrix::Matrix<galois::Galois>& G_inv, const std::vector<int>& L_nums);
		~Goppa_private();
		matrix::Matrix<galois::Galois> decode(const matrix::Matrix<galois::Galois>& y) const;

	private:
		unsigned int poly;
		matrix::Matrix<galois::Galois> g;
		matrix::Matrix<galois::Galois> H;
		matrix::Matrix<galois::Galois> Y;
		matrix::Matrix<galois::Galois> G_inv;
		std::vector<int> L_nums;
	};

	struct Goppa : public crypto::Cryptosystem {
	public:
		Goppa(const std::string &filename);
		~Goppa();
		void generate_pair(crypto::Crypto_public_key **pub_k, crypto::Crypto_private_key **priv_k) const;

	private:
		std::string filename;
	};

} // goppa

#endif // !GOPPA