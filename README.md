# RSA common factor attack

This is brief realisation of *RSA* common factor attack on SSH public keys in golang. Just create file `keys.list` with a list of RSA public keys if format:

```
<ip address> <rsa public key in ssh format>
...
```

Then:
```
go run main.go
```
