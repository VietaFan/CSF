#include <cstdio>
#include <cstdlib>
#include <string>
#define MAX_GRAPHS 13000
using namespace std;
typedef unsigned char byte;
int n = 6;
const int sizes[] = {1,1,2,4,11,34,156,1044,12346,274668,12005168};
const string filenames[] = {"","","","","","graph5.g6","graph6.g6","graph7.g6","graph8.g6","graph9.g6","graph10.g6"};
struct graph {
	byte adjMat[10][10];
};
graph graphs[MAX_GRAPHS];
int lineSize;
void processGraph(graph *g) {
	int col = 1, row = 0;
	byte next;
	scanf("%c", &next);
	for (int i=0; i<n; i++)
		g->adjMat[i][i] = 0;
	for (int i=0; i<lineSize; i++) {
		scanf("%c", &next);
		printf("%c", next);
		next -= 63;
		for (int k=32; k>0; k >>= 1) {
			g->adjMat[row][col] = ((next&k)>0);
			g->adjMat[col][row] = g->adjMat[row][col];
			row++;
			if (row == col) {
				row = 0; 
				col++;
			}
			if (col == n)
				break;
		}
	}
	scanf("%c",&next);
	printf("\n");
}
void printGraph(graph *g) {
	for (int i=0; i<n; i++) {
		printf("%d: [", i);
		for (int j=0; j<n; j++)
			if (g->adjMat[i][j])
				printf("%d, ", j);
		printf("]\n");
	}
}

int main() {
	lineSize = (n*(n-1)/2+5)/6;
	freopen(filenames[n].c_str(), "r", stdin);
	for (int i=0; i<sizes[n]; i++) {
		processGraph(graphs+i);
	}
	printGraph(graphs);
	printGraph(graphs+155);
	return 0;
}
