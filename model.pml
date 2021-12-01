

#define PLACE_NUM 2
#define USER_NUM 3

/* Еще один аргумент в виде массива или места? Другой канал? */
chan server_channel = [2] of {mtype, byte};
chan user_channel[USER_NUM] = [2] of {mtype, byte};

mtype = {
	/* user actions */
	user_send_id, user_select_place, user_purchase, request_places,
	/* server responses */
	server_send_places, server_purchase_result, success
};

proctype user(byte uid; byte place_to_choose) {
	printf("MSC: User %d\n", uid);
	
	/* send id data to server */
	server_channel ! user_send_id (uid);
	
	user_channel[uid] ? success; /* expected success response from server? */
	
	/* request for places statuses */
	server_channel ! request_places;
	
	bool places[PLACE_NUM];
	
	user_channel[uid] ? places;
	
	/* expected for place_to_choose to be free. Otherwise stack in this place */
	places[place_to_choose] == true;
	
	/* reserve place. Uid needed? */
	server_channel ! user_select_place (uid, place_to_choose);
	
	user_channel[uid] ? success;
	
	/* buy ticket */
	server_channel ! user_purchase (uid, place_to_choose);
	
	/* expect server to return uid like it is personal data */
	user_channel[uid] ? success (uid);
}

proctype server() {
	bool places[PLACE_NUM];
	
	mtype msg;
	byte uid;
	byte place; 
	
	do 
		:: server_channel ? user_send_id (uid) -> 
			action; /* save user id. send success response? */
			
		:: server_channel ? request_places -> 
			action; /* return free places */	
			
		:: server_channel ? user_select_place (uid, place) -> 
			action; /* reserve place */
			
		:: server_channel ? user_purchase (uid, place) -> 
			action; /* payment of the ticket by the user */
	od;
}

init {
	atomic {
		run server();
		run user(0);
		run user(1);
	}
}