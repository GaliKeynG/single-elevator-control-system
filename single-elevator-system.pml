#define N 10   
#define MAX_T 20
#define MAX_P 5 

// 0:stop, 1:up, -1:down
int floor = 1;
int dir = 0; 
int pass = 0; // passengers count
int goal = -1; 

// request arrays
bool r_up[N+1];
bool r_down[N+1];
bool r_in[N+1]; 

// test input
int test_seq[MAX_T+1];

// logic to find next floor
inline find_next() {
    goal = -1;
    
    // 1. check people inside
    i = 1;
    do
    :: (i <= N) ->
        if
        :: (r_in[i]) -> goal = i; goto found;
        :: else -> skip;
        fi;
        i++;
    :: (i > N) -> break;
    od;

    // 2. check people outside
    if
    :: (goal == -1) ->
        // if going up or stop, check upper floors first
        if
        :: (dir >= 0) -> 
            i = floor;
            do
            :: (i <= N) ->
                if
                :: (r_up[i] || r_down[i]) -> goal = i; goto found;
                :: else -> skip;
                fi;
                i++;
            :: (i > N) -> break;
            od;
            
            // if not found, check lower floors (from bottom)
            i = 1;
            do
            :: (i < floor) ->
                if
                :: (r_up[i] || r_down[i]) -> goal = i; goto found;
                :: else -> skip;
                fi;
                i++;
            :: (i >= floor) -> break;
            od;

        // if going down, check lower floors first
        :: (dir == -1) -> 
            i = floor;
            do
            :: (i >= 1) ->
                if
                :: (r_up[i] || r_down[i]) -> goal = i; goto found;
                :: else -> skip;
                fi;
                i--;
            :: (i < 1) -> break;
            od;

            // if not found, check upper floors (from top)
            i = N;
            do
            :: (i > floor) ->
                if
                :: (r_up[i] || r_down[i]) -> goal = i; goto found;
                :: else -> skip;
                fi;
                i--;
            :: (i <= floor) -> break;
            od;
        fi;
    :: else -> skip;
    fi;

    found: skip;
}

// read test data
inline get_input(time) {
    int val = test_seq[time];
    if
    :: (val > 0 && val <= N) ->
        printf("BTN: floor %d pressed\n", val);
        if
        :: (val < N) -> r_up[val] = 1;
        :: else -> r_down[val] = 1;
        fi;
    :: else -> skip;
    fi;
}

proctype main_ctrl() {
    int t = 0;
    int i = 0;    
    int next_f = 0; 

    // setup test cases
    test_seq[1] = 3; 
    test_seq[2] = 2; // intercept test
    test_seq[3] = 5; 
    test_seq[12] = 4;
    
    do
    :: (t < MAX_T) ->
        get_input(t);
        find_next();

        printf("T=%d | F=%d | Load=%d | Goal=%d\n", t, floor, pass, goal);

        if
        :: (goal == -1) -> 
            dir = 0;
            printf("Status: IDLE\n");
            
        :: (goal == floor) ->
            printf("Status: DOOR OPEN. ");
            
            // someone out
            if
            :: (r_in[floor]) ->
                r_in[floor] = 0;
                if :: (pass > 0) -> pass--; :: else -> skip; fi;
                printf("OUT. ");
            :: else -> skip;
            fi;
            
            // someone in
            if
            :: (r_up[floor] || r_down[floor]) ->
                r_up[floor] = 0;
                r_down[floor] = 0;
                
                if
                :: (pass < MAX_P) ->
                    pass++;
                    // sim: go to floor + 2
                    next_f = floor + 2; 
                    if :: (next_f > N) -> next_f = 1; :: else -> skip; fi;
                    r_in[next_f] = 1; 
                    printf("IN (to %d). ", next_f);
                :: else -> 
                    printf("FULL! ");
                fi;
            :: else -> skip;
            fi;
            
            printf("\n");
            // don't reset goal here, let next loop handle it
            
        :: (goal > floor && goal != -1) ->
            dir = 1;
            floor++;
            printf("Status: UP\n");
            
        :: (goal < floor && goal != -1) ->
            dir = -1;
            floor--;
            printf("Status: DOWN\n");
        fi;
        
        t++;

    :: (t == MAX_T) -> 
        printf("End.\n"); 
        break;
    od;
}

init {
    printf("Elevator Start (Max Load: %d)\n", MAX_P);
    run main_ctrl();
}

/* LTL Formulas for verification 
   Checking safety and liveness
*/

// 1. Safety: Floor must always be within range (1 to N)
ltl p_valid_floor { [] (floor >= 1 && floor <= N) }
// 2. Safety: Passengers must never exceed Max Capacity
ltl p_safe_load { [] (pass >= 0 && pass <= MAX_P) }
// 3. Logic Safety: If moving (dir is not 0), we must have a goal
ltl p_moving_valid { [] (dir != 0 -> goal != -1) }
// 4. Liveness: If we have a goal, eventually we will finish it (goal resets to -1)
ltl p_progress { [] ( (goal != -1) -> <> (goal == -1) ) }
