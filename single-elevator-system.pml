#define TOTAL_FLOORS 10
#define SIM_TIME 20
#define MAX_LOAD 5
#define STOP 0
#define UP 1
#define DOWN -1

// Global status 
int current_floor = 1;
int moving_direction = STOP;
int current_load = 0;
int next_target = -1; // -1 indicates no current target

// Floor Requests
// Promela arrays start at 0. Define size 11 to index floors 1-10 directly.
bool up_pending[TOTAL_FLOORS + 1];
bool down_pending[TOTAL_FLOORS + 1];
bool internal_request[TOTAL_FLOORS + 1]; 

// Test Sequence (Input Simulation)
int incoming_requests[SIM_TIME + 1] = {0, 3, 5, 2, 0, 9, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0};

// Inline helper to calculate the next target
// Simple scheduling logic: find the nearest request
inline calculate_target() {
    // Simplified logic: if no target exists, pick a pending request
    if (next_target == -1 || next_target == current_floor) {
        int i;
        next_target = -1; // Reset target
        
        // Priority 1: Check internal buttons (passengers inside)
        for (i : 1 .. TOTAL_FLOORS) {
            if (internal_request[i]) {
                next_target = i;
                break;
            }
        }
        // Priority 2: Check external hall calls if no internal requests
        if (next_target == -1) {
            for (i : 1 .. TOTAL_FLOORS) {
                if (up_pending[i] || down_pending[i]) {
                    next_target = i;
                    break;
                }
            }
        }
    }
}

// Inline helper to process inputs
inline handle_inputs(time) {
    int req_floor = incoming_requests[time];
    if (req_floor > 0 && req_floor <= TOTAL_FLOORS) {
        printf("[Input] User at floor %d pressed UP/DOWN\n", req_floor);
        // For simulation simplicity, assume external requests are "UP" (unless at the top floor)
        if (req_floor < TOTAL_FLOORS) {
            up_pending[req_floor] = 1;
        } else {
            down_pending[req_floor] = 1;
        }
    }
}

proctype elevator_control() {
    int clock = 0;
    
    do
    :: (clock >= SIM_TIME) -> 
        printf("=== SIMULATION OVER ===\n");
        break;
        
    :: (clock < SIM_TIME) ->
        // 1. Process inputs for the current timestamp
        handle_inputs(clock);
        
        // 2. Determine the target floor
        calculate_target();

        printf("Time %d: Floor %d | Load %d | Target %d | ", clock, current_floor, current_load, next_target);

        if
        :: (next_target == -1) -> 
            moving_direction = STOP;
            printf("Idle\n");
            
        :: (next_target == current_floor) ->
            printf("Stopping. ");
            
            // Unloading logic (Internal requests)
            if (internal_request[current_floor]) {
                printf("Passenger exit. ");
                internal_request[current_floor] = 0;
                if (current_load > 0) current_load--;
            }
            
            // Loading logic (External pending requests)
            if (up_pending[current_floor] || down_pending[current_floor]) {
                up_pending[current_floor] = 0;
                down_pending[current_floor] = 0;
                
                if (current_load < MAX_LOAD) {
                    current_load++;
                    printf("Passenger enter. ");
                    // Simulation: Passenger selects a random destination floor
                    // Logic: (current_floor + 2) wrapped around total floors
                    int dest = (current_floor + 2) % TOTAL_FLOORS; 
                    if (dest == 0) dest = 1;
                    internal_request[dest] = 1; 
                } else {
                    printf("FULL! Rejecting new passengers. ");
                }
            }
            printf("\n");
            
            // Task at this floor is complete, reset target
            next_target = -1; 
            
        :: (next_target > current_floor && next_target != -1) ->
            moving_direction = UP;
            current_floor++;
            printf("Moving UP\n");
            
        :: (next_target < current_floor && next_target != -1) ->
            moving_direction = DOWN;
            current_floor--;
            printf("Moving DOWN\n");
        fi;
        
        clock++;
    od;
}

init {
    // Initialization
    // The 'atomic' block ensures initialization completes without interruption
    atomic {
        printf("Starting Elevator System (Max Load: %d)\n", MAX_LOAD);
        run elevator_control();
    }
}
