// -*- tab-width:2 ; indent-tabs-mode:nil -*-
//:: cases SummationReduction
//:: suite problem-fail
//:: tools silicon
//:: verdict Pass

int res;

/*@
  given seq<int> ar_values;
  context \pointer(ar, N, 1\2);
  context Perm(res,write);
  context N > 0;
  context |ar_values| == N;
  context (\forall int k; 0 <= k && k < N; ar_values[k] == ar[k]);

  ensures res == (\sum int k; 0, N; ar_values[k]);
@*/
void do_sum(int N, int ar[N]) {
  res = 0;
  int tmp = 10;
  /*@ assert res == 0; @*/

  /*@
    context ar != NULL;
    context Perm(ar[i], 1\2);
    context ar_values[i] == ar[i];

    ensures  Contribution(res, ar_values[i]);
  */
#pragma omp parallel for reduction(+ : res) firstprivate(tmp)
  for (int i = 0; i < N; i++) {
    /*@ assert tmp == 10; @*/
    tmp = 15;
    res += ar[i];
  }
}
