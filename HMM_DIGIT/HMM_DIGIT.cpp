#include "stdafx.h"
#include <iostream>
#include <fstream>
#include <math.h>
#include <iomanip>
#include <vector>
#include <map>
#include <algorithm>
#include <sstream>

#include <windows.h>
//#pragma comment(lib, "windowscodecs.lib")

#define LIMIT 5000
#define FRAMES 100
#define CB_SIZE 32
#define CONVERGE_ITERATIONS 200
#define M 32
#define N 5
#define PI 3.142857142857
#define FRAME_SIZE 320
#define P 12

const int WIN_SIZE  = (FRAME_SIZE * FRAMES);
void balance();
void newoffer();
void myoffer();
void recharge();
void currentpack();
void back();
void unlimitedoffer();
void smartoffer();
void couponrecharge();
void bankrecharge();
void dfs();

int T; //Time sequence length
const int MAX_T = 150; // max time sequence length
using namespace std;

//char* B_file = "HMM_BJK_FINAL.txt";
char* B_file = "b_i_j.txt";
long double Abar[N + 1][N + 1] = {0};
int cnt = 1, train = 0;
long double Bbar[N + 1][M + 1] = {0};
long double Pibar[N + 1] = {0};
//Global variables
long double dcShift, nFactor, mx, silenceEnergy;
long double const threshold = 1e-30;   //Min threshold to be assigned to zero values in matrix B.
//char* A_file = "HMM_AIJ_FINAL.txt";
char* A_file = "a_i_j.txt";
int environment_known = 0, is_live_testing = 0;
long int sample[1000000];
long double steadySamp[WIN_SIZE];
ofstream uni, dump;
long double energy[100000];
long double Beta[MAX_T + 1][N + 1];
long double Alpha[MAX_T + 1][N + 1];
int Q[MAX_T + 1];
long double Gamma[MAX_T + 1][N + 1];
long double A[N + 1][N + 1] = {0};
int O[MAX_T + 1];
long double B[N + 1][M + 1] = {0};
long double a_average[N + 1][N + 1] = {0};
// char* PI_file = "piSir.txt";
char* PI_file = "pi.txt";
long double b_average[N + 1][M + 1] = {0};
long double pstar = 0, prev_p_star = -1;
long double Delta[MAX_T + 1][N + 1];
long double P_O_given_Model = 0;
int Psi[MAX_T + 1][N + 1];
long double Xi[MAX_T + 1][N + 1][N + 1];
long double Ai[P + 1], Ri[P + 1], Ci[P + 1];
double tokhuraWeights[] = {1.0, 3.0, 7.0, 13.0, 19.0, 22.0, 25.0, 33.0, 42.0, 50.0, 56.0, 61.0};
long double codeBook[CB_SIZE][P];
long double pi_average[N + 1] = {0};
long double Pi[N + 1] = {0};
long int sSize = 0, sampSize = 0, enSize = 0;
long double max_pobs_model = 0;
int test_ans = 0, fake = 0;

//Calculation of alpha variable to find the solution of problem number 1.
void forward_procedure() {
	int i , j , t;
	long double sum ;
	int index = O[1];
	P_O_given_Model = 0;

	for (i = 1; i <= N; i++) {
		Alpha[1][i] = Pi[i] * B[i][index];
	}

	for (t = 1; t < T; t++) {
		for (j = 1; j <= N; j++) {
			sum = 0;
			for (i = 1; i <= N; i++) {
				sum += Alpha[t][i] * A[i][j];
			}
			Alpha[t + 1][j] = sum * B[j][O[t + 1]];
		}
	}
	for (i = 1; i <= N; i++) {
		P_O_given_Model = P_O_given_Model + Alpha[T][i];
	}
}

//Calculation of alpha variable to find the solution of problem number 1.
void forward_procedure(int iteration, int kl) {
	int i , j , t;
	long double sum ;
	int index = O[1];
	P_O_given_Model = 0;

	for (i = 1; i <= N; i++) {
		Alpha[1][i] = Pi[i] * B[i][index];
	}

	for (t = 1; t < T; t++) {
		for (j = 1; j <= N; j++) {
			sum = 0;
			for (i = 1; i <= N; i++) {
				sum += Alpha[t][i] * A[i][j];
			}
			Alpha[t + 1][j] = sum * B[j][O[t + 1]];
		}
	}
	for (i = 1; i <= N; i++) {
		P_O_given_Model = P_O_given_Model + Alpha[T][i];
	}
	//finding where the model is matching
	if (P_O_given_Model > max_pobs_model) {
		max_pobs_model = P_O_given_Model;
		test_ans = iteration;
	}

	cout << "Digit:" << iteration << "\tP(obs/model) : " << P_O_given_Model << endl;
}

//function for testing with iteration as argument
void solution_to_prob1(int iteration, int kl) {
	if (kl == 0)
		forward_procedure(iteration, 0);
	else
		forward_procedure(iteration, kl);
}

//Calculation of Beta variable.
void backward_procedure() {
	int i , j , t;
	long double sum;
	int index = 0;
	for (i = 1; i <= N; i++) {
		Beta[T][i] = 1.0;
	}
	for (t = T - 1; t >= 1; t--) {
		index = O[t + 1];
		for (i = 1; i <= N; i++) {
			sum = 0;
			for (j = 1; j <= N; j++) {
				sum = sum + B[j][index] * A[i][j] * Beta[t + 1][j];
			}
			Beta[t][i] = sum;
		}
	}
}

//calculating gamma values using xita
void calculate_gamma_values() {
	int i, j, t;
	for (t = 1; t <= T - 1; t++) {
		for (i = 1; i <= N; i++) {
			Gamma[t][i] = 0;
			for (j = 1; j <= N; j++) {
				Gamma[t][i] += Xi[t][i][j];
			}
		}
	}
}

//calculating alpha and beta values
void calculate_gamma() {
	for (int t = 1; t <= T; t++) {
		for (int j = 1; j <= N; j++) {
			long double summation = 0;
			for (int k = 1; k <= N; k++) {
				summation += Alpha[t][k] * Beta[t][k];
			}
			Gamma[t][j] = (Alpha[t][j] * Beta[t][j]) / summation;
		}
	}
}

//loading the model parameters with new calculated values
void load_calculated_model() {
	int i, j;
	for (i = 1; i <= N; i++) {
		Pi[i] = Pibar[i];
	}

	for (i = 1; i <= N; i++) {
		for (j = 1; j <= N; j++) {
			A[i][j] = Abar[i][j];
		}
	}
	for (i = 1; i <= N; i++) {
		for (j = 1; j <= M; j++) {
			B[i][j] = Bbar[i][j];
		}
	}
}

void reevaluate_model_parameters() {
	int i, j, k, t;
	long double sum1 = 0 , sum2 = 0;
	//Re-evaluating Pi
	for (i = 1; i <= N; i++) {
		Pibar[i] = Gamma[1][i];
	}

	for (i = 1; i <= N; i++) {
		for (j = 1; j <= N; j++) {
			long double t1 = 0, t2 = 0;
			for (t = 1; t <= T - 1; t++) {
				t1 += Xi[t][i][j];
				t2 += Gamma[t][i];
			}
			Abar[i][j] = t1 / t2;
		}
	}
	//Re-evaluating B
	for (j = 1; j <= N; j++) {
		int count = 0;
		long double max = 0;
		int ind_j = 0, ind_k = 0;

		for (k = 1; k <= M; k++) {
			sum1 = 0 , sum2 = 0;
			for (t = 1; t < T; t++) {
				sum1 = sum1 + Gamma[t][j];
				if (O[t] == k) {
					sum2 = sum2 + Gamma[t][j];
				}
			}
			Bbar[j][k] = sum2 / sum1;

			//finding max
			if (Bbar[j][k] > max) {
				max = Bbar[j][k];
				ind_j = j;
				ind_k = k;
			}

			//updating new bij with threshold value if it is zero
			if (Bbar[j][k] == 0) {
				Bbar[j][k] = threshold;
				count++;
			}
		}
		Bbar[ind_j][ind_k] = max - count * threshold;
	}
	//loading the new model
	load_calculated_model();
}

//Adjusting Model Parameters
void calculate_xi() {

	int i , j , t , index;
	long double summation[FRAMES + 1];

	for (t = 1; t <= T; t++) {
		// index = ;
		summation[t] = 0;
		for (i = 1; i <= N; i++) {
			for (j = 1; j <= N; j++) {
				summation[t] += Alpha[t][i] * A[i][j] * B[j][O[t + 1]] * Beta[t + 1][j];
			}
		}

		for (i = 1; i <= N; i++) {
			long double x;
			for (j = 1; j <= N; j++) {
				x = Alpha[t][i] * A[i][j] * B[j][O[t + 1]] * Beta[t + 1][j];
				Xi[t][i][j] = x / summation[t];
			}
		}
	}
}

//viterbi algorithm
void viterbi() {
	//initialization
	for (int i = 1; i <= N; i++) {
		Delta[1][i] = Pi[i] * B[i][O[1]];
		Psi[1][i] = 0;
	}

	//induction
	for (int j = 1; j <= N; j++) {
		for (int t = 2; t <= T; t++) {
			long double max = 0, ti = 0;
			int ind = 0;

			for (int i = 1; i <= N; i++) {
				ti = Delta[t - 1][i] * A[i][j];
				if (ti > max) {
					max = ti;
					ind = i;
				}
			}

			Delta[t][j] = max * B[j][O[t]];
			Psi[t][j] = ind;
		}
	}

	//termination
	long double max = 0;
	for (int i = 1; i <= N; i++) {
		if (Delta[T][i] > max) {
			max = Delta[T][i];
			Q[T] = i;
		}

		pstar = max;
	}

	//backtracking
	for (int t = T - 1; t > 0; t--) {
		Q[t] = Psi[t + 1][Q[t + 1]];
	}
}

//read A
bool readA(char *filename) {
	fstream fin;
	fin.open(filename);

	//file does not exist
	if (!fin) {
		cout << "Error opening: " << filename << "\n";
		return false;
	}
	long double word;

	int row = 1, col = 1, i;
	while (fin >> word) {
		col = 1;
		A[row][col] = word;
		col++;
		for (i = 2; i <= N; i++) {
			fin >> word;
			A[row][col] = word;
			col++;
		}
		row++;
	}

	fin.close();
	return true;
}

//read B
bool readB(string filename) {
	fstream fin;
	fin.open(filename);
	if (!fin) {
		cout << "Error opening: " << filename << "\n";
		return false;
	}
	long double words;
	int row = 1, col = 1, i;
	while (fin >> words) {
		col = 1;
		B[row][col] = words;
		col++;
		for (i = 1; i < M; i++) {
			fin >> words;
			B[row][col] = words;
			col++;
		}
		row++;
	}
	fin.close();
	return true;
}

//read Pi
bool readPi(string filename) {
	fstream fin;
	fin.open(filename);
	if (!fin) {
		cout << "Error opening: " << filename << "\n";
		return false;
	}
	long double word;

	int col = 1, i;
	while (fin >> word) {
		col = 1;
		Pi[col] = word;
		col++;
		for (i = 1; i < N; i++) {
			fin >> word;
			Pi[col] = word;
			col++;
		}
	}

	fin.close();
	return true;
}

// make the model values, average model values and bar model values -  0
void erase_all_model() {
	int i, j;
	for (i = 1; i <= N; i++) {
		pi_average[i] = 0;
		Pibar[i] = 0;
		Pi[i] = 0;
		for (j = 1; j <= N; j++) {
			Abar[i][j] = 0;
			a_average[i][j] = 0;
			A[i][j] = 0;
		}
	}
	for (i = 1; i <= N; i++) {
		for (j = 1; j <= M; j++) {
			Bbar[i][j] = 0;
			b_average[i][j] = 0;
			B[i][j] = 0;
		}
	}
}

//erasing the current model
void erase_model() {
	int i, j;
	for (i = 1; i <= N; i++) {
		for (j = 1; j <= M; j++) {
			B[i][j] = 0;
		}
	}
	for (i = 1; i <= N; i++) {
		Pi[i] = 0;
		for (j = 1; j <= N; j++) {
			A[i][j] = 0;
		}
	}
}

// erasing average model
void erase_avg_model() {
	int i, j;
	for ( i = 1; i <= N; i++) {
		for ( j = 1; j <= M; j++) {
			b_average[i][j] = 0;
		}
	}
	for ( i = 1; i <= N; i++) {
		pi_average[i] = 0;
		for ( j = 1; j <= N; j++) {
			a_average[i][j] = 0;
		}
	}

}

//reading average model
void read_average_model(int digit) {

	char filename[100];

	sprintf(filename, "output/avgmodels/digit_%d_PI.txt", digit);
	readPi(filename);
	sprintf(filename, "output/avgmodels/digit_%d_B.txt", digit);
	readB(filename);
	sprintf(filename, "output/avgmodels/digit_%d_A.txt", digit);
	readA(filename);

}

//initialize model according to parameters
void initialize_model(int digit, int seq, char *filename = "--") {
	char  obs_file[100], pi_file[100], b_file[100], a_file[100];
	if (filename == "init") {
		sprintf(pi_file, "validation/Digit %d/pi_%d.txt", digit, digit);
		sprintf(b_file, "validation/Digit %d/B_%d.txt", digit, digit);
		sprintf(a_file, "validation/Digit %d/A_%d.txt", digit, digit);
		readPi(pi_file);
		readB(b_file);
		readA(a_file);
	}
	else if (filename  == "avg") {
		read_average_model(digit);
	}
	else if (filename == "--") {
		readPi(PI_file);
		readB(B_file);
		readA(A_file);
	}
}

//adding current model values to avg model
void add_to_avg_model() {
	int i, j;
	for (int i = 1; i <= N; i++) {
		for (int j = 1; j <= M; j++) {
			b_average[i][j] += B[i][j];
		}
	}
	for (i = 1; i <= N; i++) {
		pi_average[i] += Pi[i];
		for (j = 1; j <= N; j++) {
			a_average[i][j] += A[i][j];
		}
	}
}

// taking average of the avg model
void average_of_avg_model(int iter) {
	int i, j;
	for (i = 1; i <= N; i++) {
		for (j = 1; j <= M; j++) {
			b_average[i][j] /= iter;
		}
	}
	for (i = 1; i <= N; i++) {
		pi_average[i] /= iter;
		for (j = 1; j <= N; j++) {
			a_average[i][j] /= iter;

		}
	}
}

// dumping average model to file
void dump_avg_model(int digit) {
	char a_file_avg[100], b_file_avg[100], pi_file_avg[100], ind[3];
	int i, j;
	sprintf(pi_file_avg, "output/avgmodels/digit_%d_PI.txt", digit);
	FILE *fp = fopen(pi_file_avg, "w");
	for (i = 1; i <= N; i++) {
		fprintf(fp, "%Le   ", pi_average[i]);
	}
	fclose(fp);

	sprintf(a_file_avg, "output/avgmodels/digit_%d_A.txt", digit);
	FILE *fp1 = fopen(a_file_avg, "w");
	for (i = 1; i <= N; i++) {
		for (j = 1; j <= N; j++) {
			fprintf(fp1, "%Le   ", a_average[i][j]);
		}
		fprintf(fp1, "\n");
	}
	fclose(fp1);

	sprintf(b_file_avg, "output/avgmodels/digit_%d_B.txt", digit);
	ofstream fout(b_file_avg);
	for (i = 1; i <= N; i++) {
		for (j = 1; j <= M; j++) {
			fout << b_average[i][j] << "   ";
		}
		fout << endl;
	}
	fout.close();

}

//finding dc shift
void get_DC_shift(char *filename) {
	char line[80];
	int cnt = 0;
	double cEnergy = 0, cValue;
	FILE *fp;
	long int sample_count = 0;

	if (is_live_testing != 0)
		fp = fopen("silence_file.txt", "r");
	else
		fp = fopen(filename, "r");


	//	fp = fopen(filename, "r");

	if (fp == NULL) {
		printf("Not Found: Silence File\n");
		exit(1);
	}

	silenceEnergy = 0;
	dcShift = 0;
	while (!feof(fp)) {
		fgets(line, 80, fp);
		cValue = atof(line);
		dcShift += cValue;
		sample_count++;
		if (cnt == 100) {
			if (silenceEnergy < cEnergy) {
				silenceEnergy = cEnergy;
			}
			cnt = 0;
			cEnergy = 0;
		}
		cnt++;
		cEnergy += cValue * cValue;
	}
	dcShift /= sample_count;

	fclose(fp);

}

//function to setup the global variable like, max and nFactor
//max and nFactor depends on the vowel recording file and are used to do the normalization
void setupGlobal(char *filename) {
	FILE *fp;
	fp = fopen(filename, "r");
	if (fp == NULL) {
		printf("Error opening file\n");
	}
	mx = 0;
	long int totalSample = 0;
	char line[100];
	while (!feof(fp)) {
		fgets(line, 100, fp);
		if (!isalpha(line[0])) {
			if (mx < abs(atoi(line))) {
				mx = abs(atoi(line));
			}
			totalSample++;
		}
	}

	nFactor = (double)LIMIT / mx;
	//get_DC_shift();
	get_DC_shift(filename);
	fclose(fp);
}

//Calculating Tokhura's Distance Using Code Book
void calculate_tokhura_distance(long double cepstralCoeff[12], int index) {
	long double sum[CB_SIZE] = { 0 }, min = DBL_MAX;
	string temp, temp1;
	int  min_index = 0, i, j;
	for ( j = 0; j < CB_SIZE; j++) {
		for ( i = 0; i < P; i++) {
			sum[j] += (cepstralCoeff[i] - codeBook[j][i]) * (cepstralCoeff[i] - codeBook[j][i]) * tokhuraWeights[i] ;
		}
		if (sum[j] < min) {
			min_index = j;
			min = sum[j];
		}
	}
	O[index] = min_index + 1;
}


//calculating c prime values
void calculate_c_prime(double *samp) {
	int m, k;
	for ( m = 0; m <= P; m++) {
		Ri[m] = 0;
		for ( k = 0; k < FRAME_SIZE - m; k++) {
			Ri[m] += samp[k + m] * samp[k];
		}
	}

	double alpha[13][13], E[13], K[13];
	double sum = 0;
	E[0] = Ri[0];
	int i, j;
	for ( i = 1; i <= P; i++) {
		sum = 0;
		for ( j = 1; j <= i - 1; j++) {
			sum += Ri[i - j] * alpha[i - 1][j];
		}
		K[i] = (Ri[i] - sum) / E[i - 1];
		alpha[i][i] = K[i];

		for ( j = 1; j <= i - 1; j++) {
			alpha[i][j] = alpha[i - 1][j] - alpha[i - 1][i - j] * K[i];
		}
		E[i] = E[i - 1] * (1 - (K[i] * K[i])) ;
	}
	for ( i = 1; i <= P; i++) {
		Ai[i] = alpha[P][i];
	}

	Ci[0] = log(Ri[0] * Ri[0]);
	sum = 0;
	for (m = 1; m <= P; m++) {
		sum = 0;
		for (k = 1; k < m; k++) {
			sum += ( Ci[k] * k * Ai[m - k]) / (m * 1.0);
		}
		Ci[m] = sum + Ai[m] ;
	}
	sum = 0;
	for (m = 1; m <= P; m++) {
		sum = sin((PI * m) / P) * (P / 2) ;
		Ci[m] *= sum;
	}

}
void trim_digit_wave() {
	int num_frames = 0;
	int cnt = 0;

	sampSize = 0;
	int min_samples = 11200;
	if (is_live_testing == 0) {
		for (int i = 5000; i < min_samples + 5000; i++) {
			steadySamp[sampSize++] = sample[i];
		}

	}
	else {

		for (int i = 8000; i < 24000; i++) {
			steadySamp[sampSize++] = sample[i];
		}
	}

}
/*void trim_digit_wave() {
	int num_frames = 0;
	int cnt = 0;
	enSize = 0;
	double cEnergySum = 0, multiplier = 3;
	int startMarker = -1, endMarker = -1;

	for (int i = 0; i < sSize; i++) {
		double cEnergy = sample[i] * sample[i];
		if (cnt == 100) {
			energy[enSize++] = cEnergySum;
			cEnergySum = 0;
			cnt = 0;
		}
		cnt++;
		cEnergySum += cEnergy;
	}

	//printf("\nenergy - \n");
	for (int i = 0; i < enSize; i++) {
		//printf("%d: %lf\n", i, energy[i]);
	}
	int min_samples = 11200;

	for (int i = 0; i < enSize - 4; i++) {
		if (startMarker == -1 && endMarker == -1 && energy[i + 1] > multiplier * silenceEnergy && energy[i + 2] > multiplier * silenceEnergy && energy[i + 3] > multiplier * silenceEnergy && energy[i + 4] > multiplier * silenceEnergy) {
			startMarker = i * 100;
		} else if (startMarker != -1 && endMarker == -1 && energy[i + 1] <= multiplier * silenceEnergy && energy[i + 2] <= multiplier * silenceEnergy && energy[i + 3] <= multiplier * silenceEnergy && energy[i + 4] <= multiplier * silenceEnergy) {
			int diff = i * 100 - startMarker;
			if (diff < min_samples) {
				startMarker = 0 > (startMarker - (min_samples - diff) / 2) ? 0 : (startMarker - (min_samples - diff) / 2);
				endMarker = enSize * 100 < (i * 100 + (min_samples - diff) / 2) ? enSize * 100 : (i * 100 + (min_samples - diff) / 2);
			}
			else
				endMarker = i * 100;
		} else if (startMarker != -1 && endMarker != -1) break;
	}

	sampSize = 0;
	ofstream out("trim.txt");
	for (int i = startMarker; i <= endMarker; i++) {
		steadySamp[sampSize++] = sample[i];
		out << sample[i] << endl;
	}
	out.close();
	//system("pause");
}*/

//generate observation sequence
void generate_obs_sequence() {
	double fsamp[FRAME_SIZE];
	int num_frames = 0;
	int obs_ind = 1;
	
	trim_digit_wave();
	for (int i = 0; i < sampSize; i++) {
		num_frames++;
		for (int j = 0; j < 320; j++) {
			fsamp[j] = steadySamp[i];
			i++;
		}
		calculate_c_prime(fsamp);
		calculate_tokhura_distance(Ci, obs_ind++);
	}
	T = num_frames;
}

//trains the 20 files
void training() {
	erase_all_model();
	char  line[100], filename[100];
	int total_files_trained = 20;

	for (int d = 0; d <= 9; d++) {
		erase_model();

		for (int u = 1; u <=  total_files_trained; u++) {
			sprintf(filename, "input/recordings/%dE/TXT_Files/190101074_E_%d_%d.txt", d,d, u);
			//cout << "Reading " << filename << "\n";
			FILE *f = fopen(filename, "r");
			if (f == NULL) {
				printf("Error opening file: %s", filename);
				exit(1);
			}
			setupGlobal(filename);
			sSize = 0;
			while (!feof(f)) {
				fgets(line, 100, f);
				if (!isalpha(line[0])) {
					int y = atof(line);
					double normalizedX = floor((y - dcShift) * nFactor);
					sample[sSize] = normalizedX;
					sSize++;
				}
			}
			fclose(f);
			generate_obs_sequence();

			//initializing model
			if (train == 0)
				initialize_model(d, 1, "--");
			else
				initialize_model(d, 1, "avg");

			int iteration = 1;
			//starts converging model upto CONVERGE_ITERATIONS or till convergence whichever reach early
			pstar = 0, prev_p_star = -1;
			while (pstar > prev_p_star && iteration < 1000) {
				//cout<<"iteration: "<<iteration++<<endl;
				iteration++;
				prev_p_star = pstar;
				forward_procedure();
				backward_procedure();
				viterbi();

				calculate_xi();
				calculate_gamma();

				reevaluate_model_parameters();
			}

			add_to_avg_model();
		}
		average_of_avg_model(total_files_trained);
		dump_avg_model(d);
		erase_avg_model();
	}
	train++;
}

//performs live prediction of the data
void live_testing() {
	char obs_file[100], line[100];
	printf("\n Live testing \n");

	system("Recording_Module.exe 3 input.wav input_file.txt");

	initialize_model(0, 0, "--");

	FILE *f = fopen("input_file.txt", "r");
	if (f == NULL) {
		printf("Issue in opening file input_file.txt");
		exit(1);
	}
	setupGlobal("input_file.txt");

	sSize = 0;
	while (!feof(f)) {
		fgets(line, 100, f);

		//input file may contain header, so we skip it
		if (!isalpha(line[0])) {
			int y = atof(line);
			double normalizedX = floor((y - dcShift) * nFactor);
			sample[sSize++] = normalizedX;
		}
	}
	fclose(f);
	generate_obs_sequence();

	test_ans = 0;
	max_pobs_model = 0;
	for (int k = 0; k <= 9; k++) {
		read_average_model(k);
		solution_to_prob1(k, 0);
	}

	printf("\nDetected digit %d\n", test_ans);
}

//function to test the models
void testing() {
	char filename[100], line[100];
	int correctAns = 0, totalCorrectAns = 0;

	for (int d = 0; d <= 9; d++) {
		correctAns = 0;

		for (int j = 21; j <= 30; j++) {
			sprintf(filename, "input/recordings/%dE/TXT_Files/190101074_E_%d_%d.txt", d, d, j);
			//printf("\n\nInput File: %s \n", filename);

			FILE *f = fopen(filename, "r");
			if (f == NULL) {
				printf("Can't open input_file.txt");
				exit(1);
			}
			setupGlobal(filename);

			sSize = 0;
			while (!feof(f)) {
				fgets(line, 100, f);
				if (!isalpha(line[0])) {
					int y = atof(line);
					double normalizedX = floor((y - dcShift) * nFactor);
					sample[sSize++] = normalizedX;
				}
			}
			fclose(f);
			generate_obs_sequence();


			test_ans = 0;
			max_pobs_model = 0;
			for (int k = 0; k <= 9; k++) {
				read_average_model(k);
				solution_to_prob1(k, 1);
				erase_avg_model();
			}

			printf("\nPredicted digit: %d\n", test_ans);
			printf("Actual digit: %d\n", d);

			if (test_ans == d) { correctAns++, totalCorrectAns++;}
		}
		printf("Accuracy: digit %d : %lf % \n", d, 100 * (correctAns / 10.0f) );
	}

	printf("System Accuracy: %d %\n\n", totalCorrectAns);
}
string s;
// using function = std::map<string, void(*)()>;
// function mp = {
// 	{"/1", []() {balance();}},
// 	{"/2", []() {newoffer();}},
// 	{"/3", []() {myoffer();}},
// 	{"/4", []() {recharge();}},
// 	{"/11", []() {currentpack();}},
// 	{"/111", []() {back();}},
// 	{"/12", []() {back();}},
// 	{"/21", []() {unlimitedoffer();}},
// 	{"/211", []() {back();}},
// 	{"/22", []() {smartoffer();}},
// 	{"/221", []() {back();}},
// 	{"/23", []() {back();}},
// 	{"/31", []() {back();}},
// 	{"/41", []() {couponrecharge();}},
// 	{"/411", []() {back();}},
// 	{"/42", []() {bankrecharge();}},
// 	{"/421", []() {back();}},
// 	{"/43", []() {back();}},
// };

void dfs() {
	cout << "Press any number to start speaking your choice: \n";
	char c;
	cin >> c;
	cout << "\n";

	is_live_testing = 1;
	live_testing();
	is_live_testing = 0;
	if (test_ans == 0) {
		cout << "Exiting...\n";
		PlaySound(TEXT("exiting.wav"), NULL, SND_FILENAME);
		system("pause");
		exit(0);
	}

	s.push_back('0' + test_ans);

	if (s == "/1") {
		balance();
	}
	else if (s == "/2") {
		newoffer();
	}
	else if (s == "/3") {
		myoffer();
	}
	else if (s == "/4") {
		recharge();
	}
	else if (s == "/11") {
		currentpack();
	}
	else if (s == "/111") {
		back();
	}
	else if (s == "/12") {
		back();
	}
	else if (s == "/21") {
		unlimitedoffer();
	}
	else if (s == "/211") {
		back();
	}
	else if (s == "/22") {
		smartoffer();
	}
	else if (s == "/221") {
		back();
	}
	else if (s == "/23") {
		back();
	}
	else if (s == "/31") {
		back();
	}
	else if (s == "/41") {
		couponrecharge();
	}
	else if (s == "/411") {
		back();
	}
	else if (s == "/42") {
		bankrecharge();
	}
	else if (s == "/421") {
		back();
	}
	else if (s == "/43") {
		back();
	}
	s.pop_back();
	return;
}
void initt() {
	// '/1'->balance
	// '/2'->new offer
	// '/3'-> my offer
	// '/4'->Recharge
	// '/11'->current pack info
	// '/12'->back
	// '/21'->unlimited offer
	// '/22'->smart offer
	// '/23'->back
	// '/31'->back
	// '/41'->coupon Recharge
	// '/42'->payments bank
	// '/43'->back
	// '/411'->recharge with coupon take input
	// '/412'->cancel and go back

}
void balance() {

	cout << "Talktime= 0.5, validity left: 2 days\nSpeak 1: Current Pack Info\nSpeak 2: Home\n";

	//PlaySound(TEXT("balance.wav"), NULL, SND_FILENAME);
	dfs();
}
void newoffer() {

	cout << "Speak 1: Unlimited offer\nSpeak 2: Smart offers\nSpeak 3: Home\n";
	//PlaySound(TEXT("newoffers.wav"), NULL, SND_FILENAME);
	dfs();
}

void recharge() {

	cout << "Speak 1: Coupan Recharge\nSpeak 2: Bank Recharge\nSpeak 3: Home\n";

	//PlaySound(TEXT("recharge.wav"), NULL, SND_FILENAME);
	dfs();
}
void myoffer() {

	cout << "Talktime=0.5, validity left: 2 days, Data left: 200 MB, SMS left: 198\nRs. 199 Pack functional\nSpeak 1: Home\n";
	//PlaySound(TEXT("myoffer.wav"), NULL, SND_FILENAME);
	dfs();
}
void currentpack() {

	cout << "Talktime= 0.5, validity left: 2 days\nRs. 199 Pack functional\nSpeak 1: Home\n";
	//PlaySound(TEXT("currentpack.wav"), NULL, SND_FILENAME);
	dfs();

}
void unlimitedoffer() {

	cout << "Redirecting to Unlimited Offer website...\nSpeak 1: Home\n";

	//PlaySound(TEXT("unlimitedoffers.wav"), NULL, SND_FILENAME);
	dfs();
}
void smartoffer() {
	cout << "Redirecting to Smart Offer website...\nSpeak 1: Home\n";

	//PlaySound(TEXT("smartoffers.wav"), NULL, SND_FILENAME);
	dfs();
}
void couponrecharge() {

	cout << "Enter coupan code:\n";
	PlaySound(TEXT("entercoupan.wav"), NULL, SND_FILENAME);
	string s;
	cin >> s;
	cout << "Checking validity of coupan code...\nCoupan is valid... Recharged\n";
	cout << "Speak 1: Home\n";

	//PlaySound(TEXT("coupanrecharge.wav"), NULL, SND_FILENAME);
	dfs();
}

void bankrecharge() {

	cout << "Redirecting to payments.... Recharged\n";
	cout << "Speak 1: Home\n";

	//PlaySound(TEXT("bankrecharge.wav"), NULL, SND_FILENAME);
	dfs();
}
void back() {
	PlaySound(TEXT("home.wav"), NULL, SND_FILENAME);
	return;
}

int _tmain(int argc, _TCHAR* argv[]) {
	ifstream in("my_codebook.txt");
	for (int i = 0; i < CB_SIZE; i++) {
		for (int j = 0; j < P; j++) {
			in >> codeBook[i][j];
		}
	}
	in.close();
	//training();
	testing();
	system("pause");
	if (environment_known == 0) {
		printf("Testing silence\n");
		system("Recording_Module.exe 3 silence.wav silence_file.txt");
		environment_known = 1;
	}
	
	while (1) {
		
		cout << "\n\n\nSpeak 1: Balance\nSpeak 2: New offers\nSpeak 3: My Offer \nSpeak 4: Recharge\n";
		//PlaySound("root.wav", NULL, SND_SYNC);
		//PlaySound(TEXT("root.wav"), NULL, SND_FILENAME);

		s = "/";
		dfs();
	}
	return 0;
}