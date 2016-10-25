void f(int *x) {
  *x = 100;
}

int main(void){
  int a, b;
  int *p = &a;
  f(p);
  
  
  return a;
}