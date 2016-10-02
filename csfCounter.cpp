#include <cstdio>
#include <cstdlib>
#include <string>
#include <map>
#include <set>
#include <vector>
#include <algorithm>
#include <ctime>
#define MAX_GRAPHS 13000
#define MAX_N 10
#define MAX_PARTS 256
#define MAX_COEFF (1<<((MAX_N)*(MAX_N-1)/2))
#define UNCOMPUTED 0x7fffffff
using namespace std;
typedef unsigned char byte;
typedef unsigned long long u64;

int n = 7;
const int nparts[] = {1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231};

struct graph {
	byte adjMat[MAX_N][MAX_N];
	byte bitList[MAX_N*(MAX_N-1)/2];
};
struct csf {
	int coeffs[MAX_PARTS];
	int numComputed;
	bool operator<(csf other) const {
    for (int i=0; i<min(numComputed, other.numComputed); i++) {
			if (this->coeffs[i] < other.coeffs[i])
				return true;
			if (other.coeffs[i] < this->coeffs[i])
				return false;
		}
		return false;
  }
  //returns false only if the two csfs are definitely not the same (true if uncomputed)
  bool operator==(csf other) const {
  	for (int i=0; i<min(numComputed, other.numComputed); i++)
  		if (this->coeffs[i] != other.coeffs[i])
  			return false;
  	return true;
  }  	
};
struct graphCSF {
	graph g;
	csf f;
	bool operator<(graphCSF other) const {
		return this->f < other.f;
	}
};
struct partcost_t {
	int cost;
	int index;
};

const int sizes[] = {1,1,2,4,11,34,156,1044,12346,274668,12005168};
const int factorial[] = {1,1,2,6,24,120,720,5040,40320,362880,3628800};
const string filenames[] = {"graph0.g6","graph1.g6","graph2.g6","graph3.g6","graph4.g6","graph5.g6","graph6.g6","graph7.g6","graph8.g6","graph9.g6","graph10.g6"};
char* BASIS = "m";
int part[MAX_N];
vector<vector<int> > partitions;
map<vector<int>, int> partitionKey;
graph graphs[MAX_GRAPHS];
csf csfs[MAX_GRAPHS];
graphCSF graphCSFs[MAX_GRAPHS];
int numBits = n*(n-1)/2;
int lineSize = (numBits+5)/6;
partcost_t costs[MAX_PARTS]; 
int matchCounts[MAX_GRAPHS];

bool partcost_t_comp(partcost_t a, partcost_t b) {
	return a.cost < b.cost;
}
void printPartition(int partNum) {
	printf("(%d", partitions[partNum][0]);
	for (int j=1; j<partitions[partNum].size(); j++)
		printf(", %d", partitions[partNum][j]);
	printf(")\n");
}
void genPartitions(int N, int index) {
	if (N == 0) {
		vector<int> partition;
		for (int i=0; i<index; i++)
			partition.push_back(part[i]);
		partitions.push_back(partition);
		return;
	}
	int upper = N;
	if (index > 0 && part[index-1] < N)
		upper = part[index-1];
	for (int first=upper; first>0; first--) {
		part[index] = first;
		genPartitions(N-first, index+1);
	}
}
void processGraph(graph &g) {
	int col = 1, row = 0;
	int bitCount = 0;
	byte next;
	scanf("%c", &next);
	for (int i=0; i<n; i++)
		g.adjMat[i][i] = 0;
	for (int i=0; i<lineSize; i++) {
		scanf("%c", &next);
		next -= 63;
		for (int k=32; k>0; k >>= 1) {
			g.adjMat[row][col] = ((next&k)>0);
			g.adjMat[col][row] = g.adjMat[row][col];
			g.bitList[bitCount++] = g.adjMat[row][col];
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
}
void printCSF(csf &F) {
	bool first = true;
	for (int i=partitions.size()-1; i>-1; i--) {
		switch (F.coeffs[i]) {
			case 0:
				continue;
			case UNCOMPUTED:
				printf("+ ?");
				break;
			default:
				if (!first && F.coeffs[i] > 0)
					printf("+");
				if (!first)
					printf(" ");
				printf("%d", F.coeffs[i]);
				break;
		}
		first = false;
		printf("*%s[%d", BASIS, partitions[i][0]);
	  for (int k=1; k<partitions[i].size(); k++)
			printf(", %d", partitions[i][k]);
		printf("] ");
	}
	printf("\n");
}
void initCSF(csf &F) {
	//F.coeffs = vector<int>(partitions.size(), UNCOMPUTED);
	for (int i=0; i<partitions.size(); i++)
		F.coeffs[i] = UNCOMPUTED;
	F.numComputed = 0;
}

void printGraph(graph &g) {
	for (int i=0; i<n; i++) {
		printf("%d: [", i);
		for (int j=0; j<n; j++)
			if (g.adjMat[i][j])
				printf("%d, ", j);
		printf("]\n");
	}
}
bool isLessThan(int a, int b) {
	for (int i=0; i<n; i++) {
		if (partitions[a][i] < partitions[b][i])
			return true;
		if (partitions[b][i] < partitions[a][i])
			return false;
	}
	return false;
}

bool testColoring(graph &G, int *coloring) {
	for (int i=0; i<n; i++)
		for (int j=i+1; j<n; j++)
			if (G.adjMat[i][j] && coloring[i] == coloring[j])
				return false;
	return true;
}
void findNextCSFTerm(graph &G, csf &F) {
	if (F.numComputed == nparts[n])	return;
	int M[MAX_N], t, termNumber = F.numComputed;
	vector<int> L = partitions[termNumber];
	F.coeffs[termNumber] = 0;
	t = 0;
	for (int j=0; j<L.size(); j++) {
		for (int k=0; k<L[j]; k++)
			M[t++] = j;
	}
	do {
		if (testColoring(G, M))
			F.coeffs[termNumber]++;
	} while (next_permutation(M, M+n));
	F.numComputed++;
}
void findFullCSF(graph &G, csf &F) {
	for (int term=0; term<partitions.size(); term++)
		findNextCSFTerm(G,F);
}
/*
returns 1 if F1 and F2 are definitely the same
returns 0 if F1 and F2 are definitely different
otherwise, returns -1 (this means F1 and F2 are the same in all computed terms but have uncomputed terms)
*/
int checkMatch(csf &F1, csf &F2) {
	int returnVal = 1;
	for (int term=0; term<partitions.size(); term++) {
		if (F1.coeffs[term] != F2.coeffs[term] && F1.coeffs[term] != UNCOMPUTED && F2.coeffs[term] != UNCOMPUTED)
			return 0;
		if (F1.coeffs[term] == UNCOMPUTED || F2.coeffs[term] == UNCOMPUTED)
			returnVal = -1;
	}
	return returnVal;
}

int degSum(graph *g) {
	int s = 0;
	for (int i=1; i<n; i++)
		for (int j=0; j<i; j++)
			s += g->adjMat[i][j];
	s *= 2;
	return s;
}

int sqDegSum(graph *g) {
	int s = 0, k;
	for (int i=0; i<n; i++) {
		k = 0;
		for (int j=0; j<n; j++)
			if (g->adjMat[i][j])
				k++;
		s += k*k;
	}
	return s;
}

void printAllPartitions() {
	printf("All partitions of %d\n",n);
	for (int i=0; i<partitions.size(); i++) {
		printPartition(i);
	}
	printf("\n\n");
}
//sorts the partitions so that the easier ones to find coefficients for are first
void sortPartitions(int N) {
	for (int i=0; i<partitions.size(); i++) {
		costs[i].cost = factorial[N];
		costs[i].index = i;
		for (int j=0; j<partitions[i].size(); j++)
			costs[i].cost /= factorial[partitions[i][j]];
	}
	sort(costs, costs+partitions.size(), partcost_t_comp);
	vector<vector<int> > temp;
	for (int i=0; i<partitions.size(); i++)
		temp.push_back(partitions[costs[i].index]);
	partitions = temp;
}
void preparePartitions(int N) {
	partitions.clear();
	genPartitions(N, 0);
	sortPartitions(N);
	for (int i=0; i<partitions.size(); i++)
		partitionKey[partitions[i]] = i;
}
void searchMatches(graphCSF *L, int numGraphs) {
	int startPos = 0, endPos = 0, minLevel;
	sort(L,L+numGraphs);
	while (endPos < numGraphs) {
		while (endPos < numGraphs && L[startPos].f == L[endPos].f)
			endPos++;
		if (endPos > startPos+1) {
			minLevel = nparts[n];
			for (int i=startPos; i<endPos; i++) {
				findNextCSFTerm(L[i].g, L[i].f);
				if (L[i].f.numComputed < minLevel)
					minLevel = L[i].f.numComputed;
			}
			if (minLevel < nparts[n])
				searchMatches(L+startPos, endPos-startPos);
		}
		startPos = endPos;
	}
}
int computeMatchInfo(int *matchCounts) {
	searchMatches(graphCSFs, sizes[n]);
	int numCSFs = 0;
	int prev = 0;
	for (int i=1; i<=sizes[n]; i++)
		matchCounts[i] = 0;
	for (int i=1; i<sizes[n]; i++) {
		if (graphCSFs[i-1].f < graphCSFs[i].f) {
			matchCounts[i-prev]++;
			numCSFs++;
			prev = i;
		}
	}
	matchCounts[sizes[n]-prev]++;
	numCSFs++;
	return numCSFs;
}
void prepareGraphs(int N) {
	n = N;
	numBits = n*(n-1)/2;
	lineSize = (numBits+5)/6;
	freopen(filenames[n].c_str(), "r", stdin);
	for (int i=0; i<sizes[n]; i++) {
		processGraph(graphs[i]);
		initCSF(csfs[i]);
		graphCSFs[i].g = graphs[i];
		graphCSFs[i].f = csfs[i];
	}
	fclose(stdin);
}
void printResults() {
	printf("n = %d\n", n);
	printf("-----\n");
	int numCSFs = computeMatchInfo(matchCounts);
	printf("number of non-isomorphic graphs: %d\n", sizes[n]);
	printf("number of distinct CSFs: %d\n", numCSFs);
	printf("difference: %d\n", sizes[n]-numCSFs);
	printf("%d/%d ~= %f\n", sizes[n]-numCSFs, sizes[n], (0.0+sizes[n]-numCSFs)/sizes[n]);
	int s = 0;
	for (int i=1; s<numCSFs; i++) {
		printf("number of CSFs produced by exactly %d graphs: %d\n", i, matchCounts[i]);
		s += matchCounts[i];
	}
}
int main() {
	freopen("results.txt", "w", stdout);
	for (n = 1; n < 9; n++) {
		time_t t0 = clock();
		preparePartitions(n);
		prepareGraphs(n);
		printResults();
		printf("runtime: %d ms\n", clock()-t0);
	}
	fclose(stdout);
	return 0;
}



// This code is part of a previous failed attempt to compute the CSF using the p-basis and theorem 2.5.
// There's working code above that computes the CSF using the m-basis.

//int cc_graphNum, cc_cn;
//graph* cc_graph;
//csf* cc_csf;
//byte cc_state[256];
//int cg_component[MAX_N];
//int cg_counts[MAX_N+1];
//vector<int> curPart; //the current partition
///*void countGraph() {
//	for (int i=0; i<n; i++) {
//		cg_component[i] = i;
//		cg_counts[i] = 0;
//	}
//	cg_counts[n] = 0;
//	int u = 0, v = 1;
//	for (int i=0; i<numBits; i++) {
//		if (cc_state[i])
//			cg_component[v] = cg_component[u];
//		u++;
//		if (u == v) {
//			v++;
//			u=0;
//		}
//	}
//	for (int i=0; i<n; i++)
//		cg_counts[cg_component[i]]++;
//	sort(cg_counts,cg_counts+n+1);
//	vector<int> vec;
//	for (int i=n; cg_counts[i]; i--)
//		vec.push_back(cg_counts[i]);
//	for (int i=0; i<vec.size(); i++)
//		printf("%d ", vec[i]);
//	printf("\n");
//	cc_csf->coeffs[vec.size()][partitionKey[vec]] += cc_mult;
//}*/
//byte adj[MAX_N][MAX_N];
//int getPartitionNumber(int position){
//	for (int i=0; i<n; i++) {
//		cg_component[i] = i;
//		cg_counts[i] = 0;
//	}
//	cg_counts[n] = 0;
//	for (int i=0; i<n; i++)
//		for (int j=0; j<n; j++)
//			adj[i][j] = 0;
//	int u = 0, v = 1;
//	for (int i=0; i<position; i++) {
//		/*if (cc_state[i]) {
//			if (cg_component[u] < cg_component[v])
//				cg_component[v] = cg_component[u];
//			else
//				cg_component[u] = cg_component[v];
//		}*/
//		adj[u][v] = adj[v][u] = cc_state[i];
//		u++;
//		if (u == v) {
//			v++;
//			u=0;
//		}
//	}
//	for (int i=1; i<n; i++)
//		for (int j=0; j<i; j++)
//			if (adj[i][j]) {
//				if (cg_component[i] < cg_component[j])
//					cg_component[j] = cg_component[i];
//				else
//					cg_component[j] = cg_component[i];
//		}
//	for (int i=0; i<n; i++)
//		cg_counts[cg_component[i]]++;
//	sort(cg_counts,cg_counts+n+1);
//	vector<int> vec;
//	for (int i=n; cg_counts[i]; i--)
//		vec.push_back(cg_counts[i]);
//	return partitionKey[vec];
//	/*for (int i=0; i<vec.size(); i++)
//		printf("%d ", vec[i]);
//	printf("\n");*/
//	//cc_csf->coeffs[vec.size()][partitionKey[vec]] += cc_mult;
//}
//
//place in main routine:
	/*for (int i=0; i<partitions.size(); i++)
		for (int j=0; j<partitions.size(); j++)
			isStepTo[i][j] = isLessThan(i,j);*/	
//void printPartition(graph *G) {
//	int k = 0;
//	for (int i=1; i<n; i++)
//		for (int j=0; j<i; j++)
//			cc_state[k++] = G->adjMat[i][j];
//	k = getPartitionNumber(numBits);
//	printf("(%d", partitions[k][0]);
//	for (int j=1; j<partitions[k].size(); j++)
//		printf(", %d", partitions[k][j]);
//	printf(")\n");
//}
//bool isStepTo[64][64];
//void searchFrom(int position) {
//	//we've picked our edges, see if it works and if so count it
//	if (position == numBits) {
//		/*printf("(%d", partitions[getPartitionNumber(position)][0]);
//		for (int j=1; j<partitions[getPartitionNumber(position)].size(); j++)
//			printf(", %d", partitions[getPartitionNumber(position)][j]);
//		printf(")\n");*/
//		if (getPartitionNumber(position) == cc_cn) {
//			//printf("counts\n");
//			for (int i=0; i<position; i++)
//				printf("%d", cc_state[i]);
//			printf("\n");
//			int k = 0;
//			for (int i=0; i<position; i++)
//				k += cc_state[i];
//			if (k%2)
//				cc_csf->coeffs[getPartitionNumber(position)]--;
//			else
//				cc_csf->coeffs[getPartitionNumber(position)]++;
//		}
//		/*else
//			printf("doesn't count\n");*/
//		return;
//	}
//	//there's no edge here... move on
//	/*if (!cc_graph->bitList[position]) {
//		cc_state[position] = 0;
//		/*for (int i=0; i<position; i++)
//			printf(" ");
//		printf("testing with 0\n");*/
//	/*	searchFrom(position+1);
//		return;
//	}*/
//	//try it with the current edge. if it works, keep going
//	cc_state[position] = 1;
////	printf("%d %d\n", getPartitionNumber(position), cc_cn);
//	if (true) {//isStepTo[getPartitionNumber(position)][cc_cn]) { //if we can get from the current partition to the desired one by adding edges
//		/*for (int i=0; i<position; i++)
//			printf(" ");
//		printf("testing with 1\n");*/
//		searchFrom(position+1);
//	}
//	//try it without the current edge
//	cc_state[position] = 0;
///*	for (int i=0; i<position; i++)
//		printf(" ");
//	printf("testing with 0\n");*/
//	searchFrom(position+1);
//}
//	
////compute the term of coefficient number cn of the 
//void computeCoeff(int graphNum, int cn) {
//	cc_graphNum = graphNum;
//	cc_cn = cn;
//	cc_graph = &graphs[graphNum];
//	cc_csf = &csfs[graphNum];
//	for (int i=0; i<numBits; i++)
//		cc_state[i] = 0;
//	cc_csf->coeffs[cn] = 0;
//	curPart = partitions[cn];
//	searchFrom(0);
//	if ((n-curPart.size())%2)
//		csfs[graphNum].coeffs[cn] *= -1;
//}
//
//void computeFullCSF(int graphNum) {
//	/*for (int part=0; part<partitions.size(); part++) {
//		printf("going for (%d", partitions[part][0]);
//	for (int j=1; j<partitions[part].size(); j++)
//		printf(", %d", partitions[part][j]);
//	printf(")\n");
//		computeCoeff(graphNum, part);
//	}*/
//	for (int i=0; i<partitions.size(); i++)
//		csfs[graphNum].coeffs[i] = 0;
//	for (int i=0; i<(1 << numBits); i++) {
//		for (int j=0; j<numBits; j++)
//			cc_state[j] = ((i&(1<<j))>0) && graphs[graphNum].bitList[j];
//		int k = 0;
//			for (int j=0; j<numBits; j++)
//				k += cc_state[j];
//			if (k%2)
//				csfs[graphNum].coeffs[getPartitionNumber(numBits)]--;
//			else
//				csfs[graphNum].coeffs[getPartitionNumber(numBits)]++;
//	}
//}



