CXX = g++
CXXFLAGS = -std=c++17 -O2 -Wall

TARGET = ttree

SRC = src/ttree.cpp

all:
	$(CXX) $(CXXFLAGS) $(SRC) -o $(TARGET)

run:
	./$(TARGET)

fuzz:
	./$(TARGET) fuzz

clean:
	rm -f $(TARGET)