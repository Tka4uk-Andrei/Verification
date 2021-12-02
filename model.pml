#define PLACE_NUM 3
#define USER_NUM 2

typedef places_status {
	mtype status[PLACE_NUM]; // free, reserved, bought
	bool by_actual[PLACE_NUM];
	byte by[PLACE_NUM];
}; 


/* Еще один аргумент в виде массива или места? Другой канал? */
chan server_channel = [2] of {mtype, byte, byte};
chan user_channel[USER_NUM] = [1] of {mtype, byte};
chan user_channel_places[USER_NUM] = [1] of { places_status };

mtype = {
	/* user actions */
	user_send_id, user_select_place, user_purchase, request_places,
	/* server responses */
	server_send_places, server_purchase_result, success, error,
	/* place status */
	free, reserved, bought
};

proctype user(byte uid; byte place_to_choose) {
	printf("MSC: User %d want to buy place %d. Send init message.\n", uid, place_to_choose);
	/* 0 value as second argument in server_channel request - null value */
	
	/* send id data to server */
	server_channel ! user_send_id (uid, 0);
	
	user_channel[uid] ? success; /* expected success response from server? */


	printf("MSC: Sucess init message from server. User %d request for places statuses\n", uid);
	
	/* request for places statuses */
	server_channel ! request_places (uid, 0);
	
	places_status places;
	
	user_channel_places[uid] ? places;

	printf("MSC: User %d desired place %d has been purchased: %e\n", uid, place_to_choose, places.status[place_to_choose]);
	
	/* expected for place_to_choose to be free. Otherwise stack in this place */
	places.status[place_to_choose] == free;

	printf("MSC: User %d going to buy desired place %d\n", uid, place_to_choose);
	
	/* reserve place */
	server_channel ! user_select_place (uid, place_to_choose);
	
	user_channel[uid] ? success;

	printf("MSC: User %d sucessfully reserve place\n", uid);
	
	/* buy ticket */
	server_channel ! user_purchase (uid, place_to_choose);
	
	/* expect server to return uid like it is personal data */
	byte retrieved_uid;
	user_channel[uid] ? success (retrieved_uid);

	assert(retrieved_uid == uid);

	printf("MSC: User %d success :3\n", uid);
}

proctype server() {
	places_status places;
	bool users[USER_NUM];

	byte i = 0;
	do
		:: i < PLACE_NUM -> places.status[i] = free; i = i + 1;
		:: else -> break;
	od;	
	
	mtype msg;
	byte uid;
	byte place; 
	
	do 
		/* save user id. send success response? */
		/* authorize user */
		:: server_channel ? user_send_id (uid, 0) ->
			users[uid] = true;
			user_channel[uid] ! success;
			
 		/* return places statuses */
		:: server_channel ? request_places (uid, 0) ->
			if
				:: (users[uid] == true) -> user_channel_places[uid] ! places;
				:: else -> user_channel[uid] ! error; /* if user is not authorized then error response */
			fi;

		/* reserve place for user */	
		:: server_channel ? user_select_place (uid, place) -> 
			if
				:: (users[uid] == true && places.status[place] == free) -> 
					printf("MSC: Select place %d for user %d\n", place, uid);
					atomic {
						/* maybe without atomic? */
						places.status[place] = reserved;
						places.by_actual[place] = true;
						places.by[place] = uid;
					}
					
					user_channel[uid] ! success;
				:: else -> 
					/* if user is not authorized then error response */
					/* or maybe selected place is not free */
					user_channel[uid] ! error;
			fi;
			
		/* payment of the ticket by the user */	
		:: server_channel ? user_purchase (uid, place) ->
			if
				:: (
					users[uid] == true && 
					places.status[place] == reserved && 
					places.by[place] == uid && 
					places.by_actual[place] == true
					) -> 
					printf("MSC: Purchase place %d for user %d\n", place, uid);
					/* buy place */
					atomic {
						/* maybe without atomic? */
						places.status[place] = bought;
						places.by_actual[place] = true;
						places.by[place] = uid;
					}
					
					/* get uid from users array */
					user_channel[uid] ! success (places.by[place]);
				:: else -> 
					user_channel[uid] ! error; /* if user is not authorized then error response */
			fi;
	od;
}

init {
	atomic {
		run server();
		run user(0, 0);
		run user(1, 2);
	}
}