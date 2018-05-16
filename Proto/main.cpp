#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <stdexcept>
#include <tuple>
#include <vector>
#include <ctime>
#include <algorithm>
#include "galois.hpp"
#include "matrix.hpp"
#include "crypto.hpp"
#include "bch.hpp"
#include "goppa.hpp"
#include "mceliece.hpp"
#include "simple_construction.hpp"
#include "diagonal_construction.hpp"


using namespace std;
using namespace galois;
using namespace matrix;
using namespace crypto;
using namespace bch;
using namespace goppa;
using namespace mceliece;
using namespace simple_construction;
using namespace diagonal_construction;


typedef Galois gal;
typedef Matrix<gal> mgal;

void init(int& n) {
	ifstream inconfig(".config");
	string outFile;
	int randSeed;
	inconfig >> outFile >> n >> randSeed;
	inconfig.close();

	ofstream oflog(".log");

	if (randSeed < 0) {
		randSeed = time(0);
	}
	srand(randSeed);
	oflog << "srand = " << randSeed << "\n";

	if (outFile[0] != '-') {
		freopen(outFile.c_str(), "w", stdout);
	}

	oflog.close();
}

mgal str_to_mgal(const string &s) {
	int k = (int) s.size() * 8;
	mgal x(1, k);
	for (int i = 0; i < k; i++) {
		x(0, i) = Galois(((s[i / 8] >> (i % 8)) & 1), 3);
	}
	return x;
}

string mgal_to_str(const mgal &x) {
	stringstream ss;
	char c = 0;
	int k = x.size(1);
	for (int i = 0; i < k; ++i) {
		c |= (x(0, i).isZero() ? 0 : 1) << (i % 8);
		if ((i + 1) % 8 == 0) {
			ss << c;
			c = 0;
		}
	}
	if (k % 8) {
		ss << c;
	}
	return ss.str();
}

mgal get_H(const mgal& G) {
	mgal H = G;
	int k = H.size(0);
	int n = H.size(1);
	H = H.repair();
	H.inv();
	H = H.transpose();
	H = H.submatrix(k, n, 0, n);
	return H;
}

mgal infoset_attack(const mgal& G, const mgal& y, int t) {
	int k = G.size(0);
	int n = G.size(1);

	vector<int> pos(n);
	for (int i = 0; i < n; i++) {
		if (i < k) {
			pos[i] = 1;
		} else {
			pos[i] = 0;
		}
	}

	mgal G_1(k, k);
	mgal y_1(1, k);
	mgal x(1, k);
	mgal H = get_H(G).transpose();

	int cnt = -1;
	while (1) {
		cnt++;
		if (cnt > 0 && !(cnt % 50)) {
			cout << "Temporary cnt = " << cnt << endl;
		}
		if (cnt > 1000) {
			break;
		}

		random_shuffle(pos.begin(), pos.end());

		int num = 0;
		for (int i = 0; i < n; i++) {
			if (pos[i]) {
				for (int j = 0; j < k; j++) {
					G_1(j, num) = G(j, i);
				}
				y_1(0, num) = y(0, i);
				num++;
			}
		}

		G_1.safe_inv();
		x = y_1 * G_1;
		mgal y_2 = x * G + y;
		int w = 0;
		for (int i = 0; i < n; i++) {
			if (!y_2(0, i).isZero()) {
				w++;
			}
		}
        if (w <= t) {
			cout << "Final cnt = " << cnt << endl;
			return x;
        }
	}
	return x;
}

mgal sorger(const mgal& G, const mgal& M_1, const mgal& y, int t) {
	mgal M_til = M_1.repair();
	mgal M_til_inv = M_til;
	M_til_inv.inv();
	mgal G_prime = G * M_til_inv;

	int n = G_prime.size(1);
	int k = G_prime.size(0);
	int p = M_1.size(0);

	G_prime.flip(1);
	G_prime.hconcat(mgal(k));
	G_prime.eliminate(false, n - p);
	if (G_prime(n - p - 1, n - p - 1) != 1) {
		cout << "ALARM!!! (Can't attack this matrix)\n";
		ofstream oflog(".logmatrix");
		oflog << G << "\n" << M_1 << "\n";// << M << "\n";
		oflog.close();
	}
	G_prime.flip(0);
	mgal Q = G_prime.submatrix(0, k, n, n + k);
	G_prime = G_prime.submatrix(0, k, 0, n);
	G_prime.flip(1);

	mgal G_1 = G_prime.submatrix(0, k + p - n, 0, p);
	mgal G_2 = G_prime.submatrix(k + p - n, k, 0, p);

	mgal y_prime = y * M_til_inv;
	mgal y_2 = y_prime.submatrix(0, 1, p, n);
	mgal y_1 = y_prime.submatrix(0, 1, 0, p);
	y_1 -= y_2 * G_2;

	mgal u = infoset_attack(G_1, y_1, t);
	u.hconcat(y_2);

//	cout << G << "\n" << M_1 << "\n" << M << "\n" << G_prime << "\n" << Q << "\n";
//	cout << G_prime << "\n";
//	cout << Q << "\n";

	return u * Q;
}

mgal diagonal_attack(const mgal& G, const mgal& W, const mgal& y) {
	mgal W_til = W;
	mgal W_T = W.transpose();
	W_T.eliminate();

	int k = G.size(0);
	int n = G.size(1);

	int r = 0;
	for (int j = 0; j < n; ++j) {
		if (r < k && W_T(r, j) != 0) {
			if (j != r) {
				for (int i = 0; i < n; ++i) {
					W_til(r, i) = W_til(j, i);
				}
			}
			r++;
		}
	}

//	cout << r << "\n";
	int t = r;
	W_til = (W_til.submatrix(0, r, 0, n)).repair();
	W_til.inv();
	mgal new_y = y * W_til;
	W_til = G * W_til;


//	cout << W_til << "\n";
	W_til.flip(1);
	new_y.flip(1);
	W_T = W_til;
	W_T.eliminate();
//	cout << W_T << "\n";

	r = 0;
	for (int j = 0; j < n; ++j) {
		if (r < k && W_T(r, j) != 0) {
			if (j + t > n) {
				cout << "VERY BAD!\n";
			}
			if (j != r) {
				for (int i = 0; i < k; ++i) {
					W_til(i, r) = W_til(i, j);
				}
				new_y(0, r) = new_y(0, j);
			}
			r++;
		}
	}
	W_til = W_til.submatrix(0, k, 0, k);
	new_y = new_y.submatrix(0, 1, 0, k);
//	cout << W_til << "\n" << new_y << "\n";
	W_til.inv();

	new_y = new_y * W_til;
	return new_y;
//	cout << W_til << "\n";
}

void test_bch() {
	int n;
	init(n);
	BCH bch_sys(n);

	BCH_public *public_key;
	BCH_private *private_key;
	bch_sys.generate_pair((Crypto_public_key**) &public_key, (Crypto_private_key**) &private_key);

	Galois::set_binary_mode(false);

	string s = "Hello, World!";
	mgal y = public_key->encode(str_to_mgal(s));

	cout << y;
	y = public_key->add_errors(y);
	delete public_key;

	mgal x = private_key->decode(y);
	cout << y << x;// << endl;
	delete private_key;

	cout << mgal_to_str(x) << "\n";
}

void test_goppa() {
	int n;
	init(n);
	Goppa goppa(".goppa01");
	Goppa_public* public_key;
	Goppa_private* private_key;
	goppa.generate_pair((Crypto_public_key**) &public_key, (Crypto_private_key**) &private_key);

//	Galois::set_binary_mode(false);

	string s = "Hello, World!";

	mgal y = public_key->encode(str_to_mgal(s));
	cout << y;
	y = public_key->add_errors(y);
	delete public_key;
	cout << y;

	mgal x = private_key->decode(y);
	cout << x;// << endl;
	delete private_key;

	cout << mgal_to_str(x) << "\n";
}

void test_mceliece(int choice = 0) {
	int n;
	init(n);

	McEliece_public *public_key;
	McEliece_private *private_key;
	Cryptosystem *inner_cryptosystem;
	if (choice == 1) {
		inner_cryptosystem = new BCH(n);
	} else {
		inner_cryptosystem = new Goppa(".goppa01");
	}

	McEliece mceliece_sys(*inner_cryptosystem);
	mceliece_sys.generate_pair((Crypto_public_key**) &public_key, (Crypto_private_key**) &private_key);

	Galois::set_binary_mode(false);

	string s = "Hello, World!";

	mgal y = public_key->encode(str_to_mgal(s));

	mgal x = private_key->decode(y);
	cout << y << x;// << endl;
	cout << mgal_to_str(x) << "\n";

	x = infoset_attack(public_key->get_G(), y, public_key->get_t());
	cout << x;
	cout << mgal_to_str(x) << "\n";

	delete public_key;
	delete private_key;
}


void test_simple(int choice = 0) {
	Galois::set_binary_mode(false);	
	int n;
	init(n);

	Simple_public *public_key;
	Simple_private *private_key;
	Cryptosystem *inner_cryptosystem;
	if (choice == 1) {
		inner_cryptosystem = new BCH(n);
	} else {
		inner_cryptosystem = new Goppa(".goppa01");
	}


	McEliece mceliece_sys(*inner_cryptosystem);
	Simple simple_sys(mceliece_sys);

	simple_sys.generate_pair((Crypto_public_key**) &public_key, (Crypto_private_key**) &private_key);

	mgal G, M_1;
	G = public_key->get_G();
	M_1 = public_key->get_M_1();
	int t = public_key->get_t();

	string s = "Hello, World!";

	mgal y = public_key->encode(str_to_mgal(s));

	mgal x = private_key->decode(y);
	cout << y << x;// << endl;
	cout << mgal_to_str(x) << "\n";

	x = sorger(G, M_1, y, t);
	cout << x;// << endl;
	cout << mgal_to_str(x) << "\n";

	delete public_key;
	delete private_key;
}

void test_diagonal(int choice = 0) {
	Galois::set_binary_mode(false);	
	int n;
	init(n);

	Diagonal_public *public_key;
	Diagonal_private *private_key;
	Cryptosystem *inner_cryptosystem;
	if (choice == 1) {
		inner_cryptosystem = new BCH(n);
	} else {
		inner_cryptosystem = new Goppa(".goppa01");
	}


	McEliece mceliece_sys(*inner_cryptosystem);
	Diagonal diag_sys(mceliece_sys);

	diag_sys.generate_pair((Crypto_public_key**) &public_key, (Crypto_private_key**) &private_key);

	mgal G, W;
	G = public_key->get_G();
	W = public_key->get_W();

	string s = "Hello, World!";

	mgal y = public_key->encode(str_to_mgal(s));

	mgal x = private_key->decode(y);
	cout << y << x;// << endl;

	delete public_key;
	delete private_key;

	cout << mgal_to_str(x) << "\n";

	y = diagonal_attack(G, W, y);
	cout << y << endl;

	cout << mgal_to_str(y) << "\n";
}

void matroid(const Matrix<Galois> &G_0) {
	Matrix<Galois> G = G_0.transpose();    // work with rows
	int n = G.size(0);
	int k = G.size(1);
	int n_exp = 1;
	for (int i = 0; i < n; i++) {
		n_exp <<= 1;
	}

	vector<Matrix<Galois> > sums(0);
	vector<int> poss(n_exp, -1);
	int sum_num = 0;
	vector<int> s_type(n_exp, 0);

	Galois::stash_global_poly(3);

	sums.push_back(Matrix<Galois>(1, k));
	poss[0] = sum_num++;

	for (int i = 1; i < n_exp; i++) {
		int mask = 1;
		int last = -1;
		for (int j = 0; j < n; j++, mask <<= 1) {
			if (i & mask) {
				last = j;
				int prev = i & (~mask);
				if (s_type[prev]) {
					s_type[i] = 2;
					break;
				}
			}
		}

		if (s_type[i] != 2) {
			int prev = i & (~(1 << last));
			Matrix<Galois> tsum = sums[poss[prev]] + G.submatrix(last, last + 1, 0, k);
			if (tsum == sums[poss[0]]) {
				s_type[i] = 1;
			} else {
				sums.push_back(tsum);
				poss[i] = sum_num++;
			}
		}
	}

	for (int i = 0; i < n_exp; i++) {
		if (s_type[i] == 0 && __builtin_popcount(i) == k) {
			for (int j = 0; j < n; j++) {
				if (1 & (i >> j)) {
					int val = j + 1;
					if (val > 4) val++;//
					if (val > 9) val += 2;//
					cout << val << " ";
				}
			}
			cout << "\n";
		}
	}

	Galois::unstash_global_poly();
}

void test_matroid() {
	Matrix<Galois> G;
	freopen("matroid_test", "r", stdin);
	freopen("matroid_test.out", "w", stdout);
	cin >> G;
	matroid(G);
}


int main() {
//	test_bch();
//	test_goppa();
//	test_mceliece(0);
//	test_diagonal(0);
	test_simple(1);

//	test_matroid();
	return 0;
};

