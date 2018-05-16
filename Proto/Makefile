#GCC="D:\Program Files\TDM_GCC_64\bin\g++"
GCC=g++
KEYS=-Wall -std=c++11

HEAD=..\Utility\include\\
HEADKEY=-I $(HEAD)
LIB=..\Utility\src\\
BIN=..\Utility\bin\\

all: main.exe

main.exe: $(BIN)main.o $(BIN)galois.o $(BIN)crypto.o $(BIN)bch.o $(BIN)goppa.o $(BIN)mceliece.o $(BIN)simple_construction.o $(BIN)diagonal_construction.o
	$(GCC) $(BIN)galois.o $(BIN)crypto.o $(BIN)bch.o $(BIN)goppa.o $(BIN)mceliece.o $(BIN)simple_construction.o $(BIN)diagonal_construction.o $(BIN)main.o -o main.exe

$(BIN)main.o: main.cpp $(HEAD)galois.hpp $(HEAD)matrix.hpp $(HEAD)bch.hpp
	$(GCC) $(KEYS) -c main.cpp -o $(BIN)main.o $(HEADKEY)

$(BIN)galois.o: $(LIB)galois.cpp $(HEAD)galois.hpp
	$(GCC) $(KEYS) -c $(LIB)galois.cpp -o $(BIN)galois.o $(HEADKEY)

$(BIN)crypto.o: $(LIB)crypto.cpp $(HEAD)crypto.hpp
	$(GCC) $(KEYS) -c $(LIB)crypto.cpp -o $(BIN)crypto.o $(HEADKEY)

$(BIN)bch.o: $(LIB)bch.cpp $(HEAD)galois.hpp $(HEAD)matrix.hpp $(HEAD)crypto.hpp $(HEAD)bch.hpp
	$(GCC) $(KEYS) -c $(LIB)bch.cpp -o $(BIN)bch.o $(HEADKEY)

$(BIN)goppa.o: $(LIB)goppa.cpp $(HEAD)galois.hpp $(HEAD)matrix.hpp $(HEAD)crypto.hpp $(HEAD)goppa.hpp
	$(GCC) $(KEYS) -c $(LIB)goppa.cpp -o $(BIN)goppa.o $(HEADKEY)

$(BIN)mceliece.o: $(LIB)mceliece.cpp $(HEAD)galois.hpp $(HEAD)matrix.hpp $(HEAD)crypto.hpp $(HEAD)mceliece.hpp
	$(GCC) $(KEYS) -c $(LIB)mceliece.cpp -o $(BIN)mceliece.o $(HEADKEY)

$(BIN)simple_construction.o: $(LIB)simple_construction.cpp $(HEAD)galois.hpp $(HEAD)matrix.hpp $(HEAD)crypto.hpp $(HEAD)simple_construction.hpp
	$(GCC) $(KEYS) -c $(LIB)simple_construction.cpp -o $(BIN)simple_construction.o $(HEADKEY)

$(BIN)diagonal_construction.o: $(LIB)diagonal_construction.cpp $(HEAD)galois.hpp $(HEAD)matrix.hpp $(HEAD)crypto.hpp $(HEAD)diagonal_construction.hpp
	$(GCC) $(KEYS) -c $(LIB)diagonal_construction.cpp -o $(BIN)diagonal_construction.o $(HEADKEY)

clear:
	del $(BIN)*.o

