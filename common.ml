let lookup x lst =
  try
    Some (List.assoc x lst)
  with Not_found -> None
