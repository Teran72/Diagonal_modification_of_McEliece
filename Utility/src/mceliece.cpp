#include <vector>
#include <string>
#include <sstream>
#include <fstream>
#include <tuple>
#include <algorithm>
#include "galois.hpp"
#include "matrix.hpp"
#include "mceliece.hpp"
#include "crypto.hpp"

using namespace std;
using namespace galois;
using namespace matrix;
using namespace crypto;
using namespace mceliece;

McEliece_public::McEliece_public() {}

McEliece_public::McEliece_public(int t, const Matrix<Galois>& G)
	: t(t)
	, G(G) {}

McEliece_public::~McEliece_public() {}

Matrix<Galois> McEliece_public::encode(const Matrix<Galois>& message) const {
	int k = G.size(0);
	int n = message.size(1);

	Matrix<Galois> m(1, k);
	for (int i = 0; i < k; ++i) {
		m(0, i) = (i < n) ? message(0, i) : Galois(0, 3);
	}

	m *= G;
	n = m.size(1);

	vector<Galois> err(0);
	for (int i = 0; i < n; i++) {
		err.push_back(Galois((i < t) ? 1 : 0, 3));
	}
	random_shuffle(err.begin(), err.end());
	return m + (Matrix<Galois>)err;
}

Matrix<Galois> McEliece_public::get_G() const {
	return G;
}

int McEliece_public::get_n() const {
	return G.size(1);
}

int McEliece_public::get_k() const {
	return G.size(0);
}
int McEliece_public::get_t() const {
	return t;
}




McEliece_private::McEliece_private() {}

McEliece_private::McEliece_private(const Matrix<Galois>& M_inv,
			const Matrix<Galois>& P_inv,
			const Crypto_private_key* decoder)
	: M_inv(M_inv)
	, P_inv(P_inv)
	, decoder(decoder) {}

McEliece_private::~McEliece_private() {}

Matrix<Galois> McEliece_private::decode(const Matrix<Galois>& y) const {
	Matrix<Galois> ans;
	ans = y * P_inv;

	ans = decoder->decode(ans);

	return ans * M_inv;
}




McEliece::McEliece(const Cryptosystem &_decoder) {
	decoder = &_decoder;
}

McEliece::~McEliece() {}

void McEliece::generate_pair(Crypto_public_key **pub_k, Crypto_private_key **priv_k) const {
	Crypto_public_key *inner_pub_k;
	Crypto_private_key *inner_priv_k;
	
	decoder->generate_pair(&inner_pub_k, &inner_priv_k);

	Matrix<Galois> G_0 = inner_pub_k->get_G();
	int n = G_0.size(1);
	int k = G_0.size(0);
	int t = inner_pub_k->get_t();

	Galois::stash_global_poly(3);
	Matrix<Galois> M = Matrix<Galois>::randInvertible(k);
	Matrix<Galois> P = Matrix<Galois>(n, n);

	vector<int> perm(n, 0);
	for (int i = 0; i < n; i++) {
		perm[i] = i;
	}
	random_shuffle(perm.begin(), perm.end());

	for (int i = 0; i < n; i++) {
		P(i, perm[i]) = Galois(1, 3);
	}

	G_0 = M * G_0 * P;

	M.inv();
//	P.inv();
//	P = P.transpose();
	for (int i = 0; i < n; i++) {
		P(i, perm[i]) = Galois(0, 3);
	}
	for (int i = 0; i < n; i++) {
		P(perm[i], i) = Galois(1, 3);
	}

	*pub_k = new McEliece_public(t, G_0);
	*priv_k = new McEliece_private(M, P, inner_priv_k);
	delete inner_pub_k;

	Galois::unstash_global_poly();
}
