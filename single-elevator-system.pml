#define TOTAL_FLOORS 10
#define SIM_TIME 20
#define NO_REQ 99
#define MAX_LOAD  5

//Global status 
int current_floor = 1;
int moving_direction = 0;     //moving direction: 0 stop/1 up/-1 down
int door_is_open = 0;        //door status: 0 close/1 open
int current_load = 0；

//Mark which floor need to stop
int up_pending[TOTAL_FLOORS+1];
int down_pending[TOTAL_FLOORS+1];

//Request for the farthest floor
int farthest_up = 1;
int farthest_down = TOTAL_FLOORS;

//Testing sequence: SIM_TIME 20 
int incoming_requests[SIM_TIME+1] = {3, 5, 2, 1, 9, 99, 99, 99, 99, 99, 99, 99, 4};

#define QUEUE_SIZE 50
int queue[QUEUE_SIZE];
int front = 0；
int rear = 0;
int isempty = 0;

proctype elevator_control(){
    int clock =0;
    door
    :: (clock >= SIM_TIME) ->
    printf("TEST OVER\n");
    break;
    ::(clock < SIM_TIME) -> // do the current request first
    run handle_requests(clock);
    
    if 
    :: (next_target == -1) -> // if no request keep stay
    moving_direction = 0;
    door_is_open = 0;
    printf("Time%d: Elevator free, current floor%d\n", clock, current_floor);
    :: (next_target == current_floor) ->
    door_is_open = 1;
    printf("Time%d: Elevator stopby%dwhich floor\n", clock, current_floor);

    // do the request at current floor
    if (internal_request[current_floor] == 1){
        printf("do the inner request, passengers leave\n");
        internal_request[current_floor] = 0;
    }
    if (up_pending[current_floor] == 1){
        printf("do the up requests\n");
        up_pending[current_floor] = 0;
    }
    if (down_pending[current_floor] == 1){
        printf("do the down requests\n");
        down_pending[current_floor] = 0;
    }
}

