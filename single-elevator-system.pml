#define N 10   
#define MAX_T 40  
#define MAX_P 5 

// 0:stop, 1:up, -1:down
int floor = 1;
int dir = 0; 
int pass = 0; 
int goal = -1; 

// request arrays
bool r_up[N+1];
bool r_down[N+1];
bool r_in[N+1]; 

// test input buffer
int test_seq[MAX_T+1];

// logic: find next floor (SCAN)
inline find_next() {
    goal = -1;
    
    // 1. Priority: Current floor (Hold Door Logic)
    // If someone is here, stay here.
    if
    :: (r_in[floor] || r_up[floor] || r_down[floor]) -> 
        goal = floor;
    :: else -> skip;
    fi;

    // 2. Scan for targets
    if
    :: (goal == -1) ->
        // CASE: UP or IDLE
        if
        :: (dir >= 0) -> 
            // Scan UP
            i = floor;
            do
            :: (i <= N) ->
                if :: (r_in[i] || r_up[i] || r_down[i]) -> goal = i; break;
                :: else -> skip; fi;
                i++;
            :: (i > N) -> break;
            od;
            
            // Wrap around (Bottom up)
            if :: (goal == -1) ->
                i = 1;
                do
                :: (i < floor) ->
                    if :: (r_in[i] || r_up[i] || r_down[i]) -> goal = i; break;
                    :: else -> skip; fi;
                    i++;
                :: (i >= floor) -> break;
                od;
            :: else -> skip; fi;

        // CASE: DOWN
        :: (dir == -1) -> 
            // Scan DOWN
            i = floor;
            do
            :: (i >= 1) ->
                if :: (r_in[i] || r_up[i] || r_down[i]) -> goal = i; break;
                :: else -> skip; fi;
                i--;
            :: (i < 1) -> break;
            od;

            // Wrap around (Top down)
            if :: (goal == -1) ->
                i = N;
                do
                :: (i > floor) ->
                    if :: (r_in[i] || r_up[i] || r_down[i]) -> goal = i; break;
                    :: else -> skip; fi;
                    i--;
                :: (i <= floor) -> break;
                od;
            :: else -> skip; fi;
        fi;
    :: else -> skip;
    fi;
}

// read inputs
inline get_input(time) {
    int val = test_seq[time];
    if
    :: (val > 0 && val <= N) ->
        printf("BTN: floor %d pressed\n", val);
        // simple logic for up/down buttons
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

    // --- OVERLOAD SCENARIO ---
    // Simulating a queue of 7 people at Floor 1
    // They arrive one by one from T=1 to T=7
    i = 1;
    do
    :: (i <= 7) ->
        test_seq[i] = 1; 
        i++;
    :: (i > 7) -> break;
    od;
    
    // Also, someone at Floor 8 is waiting (to prove elevator leaves)
    test_seq[10] = 8; 

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
            
            // step 1: unload
            if
            :: (r_in[floor]) ->
                r_in[floor] = 0;
                if :: (pass > 0) -> pass--; :: else -> skip; fi;
                printf("OUT. ");
            :: else -> skip;
            fi;
            
            // step 2: load
            if
            :: (r_up[floor] || r_down[floor]) ->
                // Note: We clear the flag, meaning we "processed" the button press
                r_up[floor] = 0;
                r_down[floor] = 0;
                
                // --- THE DECISION LOGIC ---
                if
                :: (pass < MAX_P) ->
                    pass++;
                    // sim: passenger goes to floor 5
                    next_f = 5; 
                    r_in[next_f] = 1; 
                    printf("IN (to %d). ", next_f);
                :: else -> 
                    // DECISION: REJECT
                    printf("FULL! Rejected. ");
                fi;
            :: else -> skip;
            fi;
            
            printf("\n");
            
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
