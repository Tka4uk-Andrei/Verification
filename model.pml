#define PLACE_NUM 2
#define USER_NUM 2

typedef places_status {
	mtype status[PLACE_NUM]; // free, reserved, bought
	bool by_actual[PLACE_NUM];
	byte by[PLACE_NUM];
}; 


chan server_channel = [10] of {mtype, byte, byte};
chan user_channel[USER_NUM] = [2] of {mtype};
chan user_channel_uid[USER_NUM] = [2] of {mtype, byte};
chan user_channel_places[USER_NUM] = [2] of { places_status };


places_status places;
bool users[USER_NUM];
byte purchases = 0;
byte active_users = 0;

mtype = {
	/* user actions */
	start_session, user_select_place, user_purchase, request_places, end_session,
	/* server responses */
	server_send_places, server_purchase_result, success, error,
	/* place status */
	free, reserved, bought
};

proctype user(byte uid; byte place_to_choose) {
	places_status received_places;
	byte places_fail = 0;
	byte wait_times = 0;
	bool in_connection = false;

	printf("MSC: User %d send init message to server.\n", uid);
	
	/* Start session. Send id data to server */
	/* 0 value as second argument in server_channel request - null value */
	in_connection = true;
	server_channel ! start_session (uid, 0);
	
	/* expected success response from server */
	user_channel[uid] ? success;

	printf("MSC: User %d request for places statuses\n", uid);
	
	/* request for places statuses */
	select_place_label: server_channel ! request_places (uid, 0);
	
	user_channel_places[uid] ? received_places;

	printf("MSC: User %d desired place %d has status %e\n", uid, place_to_choose, received_places.status[place_to_choose]);
	
	/* expected for place_to_choose to be free. Otherwise select new place */
	mtype place_status = received_places.status[place_to_choose];
	if
		:: place_status == free -> 
			skip;
		:: place_status != free ->
			if
				:: place_to_choose < PLACE_NUM -> place_to_choose++;
				:: place_to_choose >= PLACE_NUM -> place_to_choose = 0;
			fi;
			places_fail++;
			if
				:: places_fail == PLACE_NUM -> goto end_session_label;
				:: places_fail != PLACE_NUM -> skip;
			fi;
			printf("MSC: Selected by user %d place is bought. Select new one %d\n", uid, place_to_choose);
			goto select_place_label;
	fi;
	
	end: place_status == free;

	printf("MSC: User %d is going to buy place %d\n", uid, place_to_choose);
	
	/* reserve place */
	server_channel ! user_select_place (uid, place_to_choose);
	
	if
		:: user_channel[uid] ? success -> skip;
		:: user_channel[uid] ? error -> goto select_place_label;
	fi;	

	printf("MSC: User %d sucessfully reserve place\n", uid);
	
	/* buy ticket */
	server_channel ! user_purchase (uid, place_to_choose);
	
	/* expect server to return uid like it is personal data */
	byte retrieved_uid;
	user_channel_uid[uid] ? success (retrieved_uid);

	assert(retrieved_uid == uid);

	printf("MSC: User %d successfully buy ticket :3\n", uid);

	end_session_label: server_channel ! end_session (uid, 0);

	atomic {
		user_channel[uid] ? success;
		in_connection = false;
	}

	printf("MSC: User %d end session\n", uid);
}

proctype server() {	
	mtype msg;
	byte uid;
	byte place; 
	
	do 
		/* authorize user, save user id */
		:: server_channel ? start_session (uid, 0) ->
			if
				:: users[uid] == false -> 
					atomic {
						users[uid] = true;
						active_users++;
					}

					user_channel[uid] ! success;
				:: users[uid] == true -> 
					/* if user already authorizes then error response */
					user_channel[uid] ! error;
			fi;

		/* end session */
		:: server_channel ? end_session (uid, 0) ->
			if
				:: users[uid] == true -> 
					atomic {
						users[uid] = false; 
						active_users--;
					}
					user_channel[uid] ! success;
				:: users[uid] == false -> 
					/* if user is not authorized then error response */
					user_channel[uid] ! error;
			fi;
			
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
						places.status[place] = bought;
						purchases++;
					}
					
					/* get uid from users array */
					user_channel_uid[uid] ! success (places.by[place]);
				:: else -> 
					/* if user is not authorized then error response */
					user_channel[uid] ! error;
			fi;

		:: (purchases == PLACE_NUM || purchases == USER_NUM) && active_users == 0 && len(server_channel) == 0 ->
				printf("MSC: All places are sold out!\n");
				break;
	od;
}

init {
	assert (USER_NUM <= PLACE_NUM);

	atomic {
		/* init places */
		byte i = 0;
		do
			:: i < PLACE_NUM -> places.status[i] = free; places.by_actual[i] = false; i++;
			:: else -> break;
		od;	

		run server();	

		/* Simulation 1 */
		i = 0;
		do
			:: i < USER_NUM -> run user(i, i); i++;
			:: else -> break;
		od;

		/* Simulation 2 */
		// run user(0, 0);
		// run user(1, 0);
	}
}

/* По умолчанию пользователь хочет купить место, совпадающее с его id */

/* Один пользователь - один билет. Любой пользователь купит билет.
   Если пользователей меньше, чем билетов, то наступит состояние, */
/* когда количество покупок всегда будет равно количеству пользователей */
ltl all_tickets_bought { [] (USER_NUM <= PLACE_NUM -> <> [] (purchases == USER_NUM)) }

/* Когда все пользователи купили билеты, то они завершают сессию */
ltl f0 { [] (USER_NUM <= PLACE_NUM && purchases == USER_NUM -> <> [] (active_users == 0)) }

/* У любых двух пользователей не может быть одинаковых мест; */
/* Если место было куплено пользователем, то это окончательно и другой пользователь не займет его */
ltl f1 { [] ((places.status[0] == bought && places.by[0] == 0) -> [] (places.by[0] == 0)) }

/* Если место было зарезервировано пользователем, то это окончательно и другой пользователь не займет его */
ltl f2 { [] ((places.status[1] == reserved && places.by[1] == 1) -> [] (places.by[1] == 1)) }

/* Если в самолёте есть свободные места, то пользователь точно его может выбрать, 
то есть например система не вернёт ошибку о том, что оно занято;*/
ltl f3 { <> [] (places.by[0] == 0 && places.status[0] == bought) }

/* Место может быть либо свободным, либо зарезервированным, либо купленным */
/* Какой-то странный статус 0 появляется */
ltl f4 { [] (places.status[0] == free || places.status[0] == reserved || places.status[0] == bought || places.status[0] == 0)}

/* Если паспортные данные не были введены, то нельзя перейти к процессу выбора места и оплаты; */
ltl f5 { [] (user[1]:in_connection == true && users[1] == false -> places.by[1] != 1)}

/* На время соединения с сайтом у него есть личные данные пользователя ; */
ltl f6 { [] (user[1]:in_connection == true -> users[1] == true)}
ltl f7 { [] (users[1] == false -> user[1]:in_connection == false)}

/* Пользователь не может купить два места */
ltl f8 { ![] (places.by[0] == 0 && places.by[1] == 0)}
ltl f9 { ![] (places.by[0] == 1 && places.by[1] == 1)}
