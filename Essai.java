class Essai {

    void f() {
        int n = 10;
        int j = 0;
        for (int i=0; i<n; i++) j = j+2;
        // sawja.Assertions.check(j == 2*n);
    }

    void g() {
        int x = 0;
        int j = 0;
        if (j == 0) {
            while (j == 0) {
                j += 0;
            }
            int a = 1;
        }
        else {
            int a = 1;
        }
        int y = 10 / x;
        if (x == 8) {
            int a = 5;
        }
        y = j;
    }

    void h() {
      int x = 0;
      int j = 10;
      int b = 1;
      if (x == 0) {
        x = 10;
      }
      else {
        x = 12;
      }
      if (x > 0) {
        b = 1;
      }
      else {
        b = 2;
      }
      x += 1;
      j+= 1;
    }

    void two_times_loop() {
      int i = 0;
      int j = 0;
      while (i < 10) {
        i += 1;
        j += 1;
      }
      int r = j;
      if (i == 2) {
        int a = 1;
      }
      r = j + 1;
    }

    void running() {
      int i = 0;
      int j = 0;
      while (i < 10) {
        i += 1;
        int x = (int)Math.random();
        if (x == 0) {
          j += 1;
        }
        else {
          j += 2;
        }
      }
      int r = j;
      int b = (int)Math.random();
      if (b == 0) {
        int a = 1;
      }
      r = j + 1;
    }
}
